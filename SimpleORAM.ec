(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv Distr DBool DList DInterval FMap FSet RealExp.
require import StdOrder StdBigop.
require import Finite IntMin Array BitEncoding.
(*---*) import BS2Int.
require (*--*) BitWord.
(*---*) import IntOrder Bigint.

(* -------------------------------------------------------------------- *)
op "_.[_]" ['a] (s : 'a list) (i : int) : 'a =
  nth witness s i.

op "_.[_<-_]" ['a] (s : 'a list) (i : int) (x : 'a) : 'a list =
  mkseq (fun k => if i = k then x else s.[k]) (size s).

op isprefix ['a] (p1 : 'a list) (p2 : 'a list) : bool =
  size p1 <= size p2 /\ p1 = take (size p1) p2.

op prefixes ['a] (path : 'a list) =
  map (fun i => take i path) (range 0 (size path + 1)).

(* -------------------------------------------------------------------- *)
theory SimpleORAM.
  type value.

  type cell.

  type path   = bool list.
  type block = cell * path * value.

  op index_of_path (p : path) : int =
    bs2int (true :: p).

  op int2path (i : int) : path =
    drop 1 (int2bs (ceil (log2 i%r)) (i - 1)).

  op K: int.
  axiom K_ge0 : 0 <= K.
  axiom K2_gt1 : 0 < K %/ 2 - 1.

  (* -------------------------------------------------------------------- *)
  type oram = {
    height    : int;
    bucket    : path -> block list;
    positions : cell -> path;
  }.

  (* -------------------------------------------------------------------- *)
  type inst = [
    | Rd of cell
    | Wt of (cell * value)
  ].
  type prog = inst list.

  op isRd(i : inst) =
    with i = Rd c => true
    with i = Wt c => false.

  op isWt(i : inst) =
    with i = Rd _ => false
    with i = Wt _ => true.

  op varV(i : inst) =
    with i = Rd c => c
    with i = Wt cv => cv.`1.

  (* -------------------------------------------------------------------- *)
  type opkind = [Read | Write].
  type leakage = opkind * path.

  (* -------------------------------------------------------------------- *)
  module ORAM = {
    var leakage  : leakage list
    var int_overflow : bool
    var leaf_overflow : bool

    proc fetch(oram : oram, c : cell) : oram * block = {
      var i, j : int;
      var ps   : path;
      var v    : block option;
      var pos  : path;

      pos <- oram.`positions c;
      v   <- None;
      i   <- 0;

      while (i <= oram.`height) {
        ps      <- take i pos;
        j       <- find (fun x : block => x.`1 = c) (oram.`bucket ps);
        leakage <- (Read, ps) :: leakage; (* tree reading *)

        if (j < size (oram.`bucket ps)) {
          v <- Some (oram.`bucket ps).[j];
          oram <- {| oram with bucket =
            oram.`bucket.[ps <- trim (oram.`bucket ps) j]
          |};
        }

        (* even when not found, leaking is always. *)
        leakage <- (Write, ps) :: leakage;
        
        i <- i + 1;
      }

      return (oram, oget v);
    }

    proc putback(oram : oram, b : block) : oram = {
      var root : block list;

      root    <- oram.`bucket [] ++ [b];
      if (K <= (size root)) {
        if (1 < oram.`height) {
          int_overflow <- true;
        } else {
          leaf_overflow <- true;
        }
      }
      oram    <- {| oram with bucket = oram.`bucket.[[] <- root] |};
      leakage <- (Write, []) :: leakage;
      return oram;
    }

    proc flush(oram : oram) : oram = {
      var i      : int;
      var p      : path;
      var ps     : path;
      var pushed : block list;
      var pback  : block list;

      p <$ dlist {0,1} oram.`height;
      pushed <- [];

      i <- 0;
      while (i <= oram.`height) {
        ps      <- take i p;
        pushed  <- pushed ++ oram.`bucket ps;
        leakage <- (Read, ps) :: leakage;

        pback <- if i = oram.`height 
                 then pushed
                 else filter (fun block : block =>
                          (take (i+1) block.`2) <> (take (i+1) p)
                      ) pushed;

        pushed <- if i = oram.`height 
                 then []
                 else filter (fun block : block =>
                         (take (i+1) block.`2) = (take (i+1) p)
                      ) pushed;

        if (K <= size pback) {
          if (i < oram.`height) {
            int_overflow <- true;
          } else {
            leaf_overflow <- true;
          }
        }

        oram    <- {| oram with bucket = oram.`bucket.[ps <- pback]; |};
        leakage <- (Write, ps) :: leakage;

        i <- i + 1;
      }

      return oram;
    }

    proc oread(oram : oram, c : cell) : oram * value = {
      var block : block;
      var pos  : path;

      (oram, block) <@ fetch(oram, c);
      pos  <$ dlist {0,1} oram.`height;
      oram <- {| oram with positions = oram.`positions.[c <- pos] |};
      oram <@ putback(oram, (c, pos, block.`3));
      oram <@ flush(oram);

      return (oram, block.`3);
    }

    proc owrite(oram : oram, c : cell, v : value) : oram = {
      var block : block;
      var pos  : path;
      var tmpo : oram option;
      var aout : (oram * value option) option;

      (oram, block) <@ fetch(oram, c);
      pos  <$ dlist {0,1} oram.`height;
      oram <- {| oram with positions = oram.`positions.[c <- pos] |};
      oram <@ putback(oram, (c, pos, v));
      oram <@ flush(oram);

      return oram;
    }

    proc compile(o : oram, p : prog) : oram * (value list) = {
      var i : int;
      var v : value;
      var os : value list;
      i <- 0;
      os <- [];
      while (i < size p) {
        match (nth witness p i) with
        | Rd c => { (o, v) <@ oread(o, c); os <- v :: os; }
        | Wt t => { o <@ owrite(o, t.`1, t.`2); }
        end;
        i <- i + 1;
      }
      return (o, os);
    }
  }.

  module ORAM_Tape = {
    var leakage  : leakage list
    var int_overflow : bool
    var leaf_overflow : bool
    var random_tape : bool list

    proc sample(n : int) : path = {
      var bs : path;
      var b : bool;
      var k : int;
      k <- 0;
      bs <- [];
      while (k < n) {
        b <- head witness random_tape;
        random_tape <- behead random_tape;
        bs <- bs ++ [b];
      }
      return bs;
    }

    proc fetch(oram : oram, c : cell) : oram * block = {
      var i, j : int;
      var ps   : path;
      var v    : block option;
      var pos  : path;

      pos <- oram.`positions c;
      v   <- None;
      i   <- 0;

      while (i <= oram.`height) {
        ps      <- take i pos;
        j       <- find (fun x : block => x.`1 = c) (oram.`bucket ps);
        leakage <- (Read, ps) :: leakage; (* tree reading *)

        if (j < size (oram.`bucket ps)) {
          v <- Some (oram.`bucket ps).[j];
          oram <- {| oram with bucket =
            oram.`bucket.[ps <- trim (oram.`bucket ps) j]
          |};
        }

        (* even when not found, leaking is always. *)
        leakage <- (Write, ps) :: leakage;

        i <- i + 1;
      }

      return (oram, oget v);
    }

    proc putback(oram : oram, b : block) : oram = {
      var root : block list;

      root    <- oram.`bucket [] ++ [b];
      if (K <= (size root)) {
        if (1 < oram.`height) {
          int_overflow <- true;
        } else {
          leaf_overflow <- true;
        }
      }
      oram    <- {| oram with bucket = oram.`bucket.[[] <- root] |};
      leakage <- (Write, []) :: leakage;
      return oram;
    }

    proc flush(oram : oram) : oram = {
      var i      : int;
      var p      : path;
      var ps     : path;
      var pushed : block list;
      var pback  : block list;

      p <@ sample(oram.`height);
      pushed <- [];

      i <- 0;
      while (i <= oram.`height) {
        ps      <- take i p;
        pushed  <- pushed ++ oram.`bucket ps;
        leakage <- (Read, ps) :: leakage;

        pback <- if i = oram.`height
                 then pushed
                 else filter (fun block : block =>
                          (take (i+1) block.`2) <> (take (i+1) p)
                      ) pushed;

        pushed <- if i = oram.`height
                 then []
                 else filter (fun block : block =>
                         (take (i+1) block.`2) = (take (i+1) p)
                      ) pushed;

        if (K <= size pback) {
          if (i < oram.`height) {
            int_overflow <- true;
          } else {
            leaf_overflow <- true;
          }
        }

        oram    <- {| oram with bucket = oram.`bucket.[ps <- pback]; |};
        leakage <- (Write, ps) :: leakage;

        i <- i + 1;
      }

      return oram;
    }

    proc oread(oram : oram, c : cell) : oram * value = {
      var block : block;
      var pos  : path;

      (oram, block) <@ fetch(oram, c);
      pos  <@ sample(oram.`height);
      oram <- {| oram with positions = oram.`positions.[c <- pos] |};
      oram <@ putback(oram, (c, pos, block.`3));
      oram <@ flush(oram);

      return (oram, block.`3);
    }

    proc owrite(oram : oram, c : cell, v : value) : oram = {
      var block : block;
      var pos  : path;
      var tmpo : oram option;
      var aout : (oram * value option) option;

      (oram, block) <@ fetch(oram, c);
      pos  <@ sample(oram.`height);
      oram <- {| oram with positions = oram.`positions.[c <- pos] |};
      oram <@ putback(oram, (c, pos, v));
      oram <@ flush(oram);

      return oram;
    }

    proc compile(o : oram, p : prog, C : cell list) : oram * (value list) = {
      var i, j : int;
      var v : value;
      var os : value list;
      var bs : bool list;
      var b : bool;

      (* sample random tapes *)
      random_tape <- [];
      j <- 0;
      while (j < (size C) * o.`height) {
        b <$ dbool;
        random_tape <- random_tape ++ [b];
        j <- j + 1;
      }
      j <- 0;
      while (j < (o.`height * size p)) {
        b <$ dbool;
        random_tape <- random_tape ++ [b];
        j <- j + 1;
      }

      (* initialize position map *)
      j <- 0;
      while (j < (size C)) {
        bs <@ sample(o.`height);
        o <- {|  height = o.`height;
                 bucket = o.`bucket;
                 positions = o.`positions.[C.[j] <- bs];
             |};
      }

      i <- 0;
      os <- [];
      while (i < size p) {
        match (nth witness p i) with
        | Rd c => { (o, v) <@ oread(o, c); os <- v :: os; }
        | Wt t => { o <@ owrite(o, t.`1, t.`2); }
        end;
        i <- i + 1;
      }
      return (o, os);
    }
  }.

  (* -------------------------------------------------------------------- *)
  op is_oram (C : cell -> bool) (o : oram) =
       (* we have at least two levels *)
       0 < o.`height

       (* There is nothing below the leafs *)
    && (forall (p : path), o.`height < size p => o.`bucket p = [])

       (* Well formness of the positions map: all paths of correct size *)
    && (forall (p : path), (exists c, p = o.`positions c) => size p = o.`height)

       (* only cells in the map are on the tree *)
    && (forall (p : path), size p <= o.`height =>
          (forall block, block \in o.`bucket p =>
              (C block.`1)))

       (* Path invariant: there exists a block holding the cell in the path
          to its position *)
    && (forall (c : cell), C c =>
          let p = o.`positions c in
          (exists i, 0 <= i <= o.`height &&
            let block = o.`bucket (take i p) in
            has (fun (block : block) => block.`1 = c /\ block.`2 = p) block))

       (* Duplicates freeness: take any two bucket: same cell implies same block *)
    && (forall (p1 p2 : path),
          let bucket1 = o.`bucket p1 in
          let bucket2 = o.`bucket p2 in
           forall i1 i2, 0 <= i1 < size bucket1 => 0 <= i2 < size bucket2 =>
             let bucket1 = bucket1.[i1] in
             let bucket2 = bucket2.[i2] in
             bucket1.`1 = bucket2.`1 => p1 = p2 /\ i1 = i2)

       (* Well formness of bucket: bucket contain correct position for held cell *)
    && (forall (p : path), (size p <= o.`height) =>
          forall i, 0 <= i <= o.`height =>
            let block = o.`bucket (take i p) in
            forall (b : block), b \in block =>
              o.`positions b.`1 = b.`2 && 
              take (if i <= size p then i else size p) b.`2 = 
                take (if i <= size p then i else size p) p).

   lemma is_oram_height_gt0 (C : cell -> bool) (oram : oram) :
     is_oram C oram => 0 < oram.`height.
   proof. by move=> @/is_oram. qed.

   lemma is_oram_height_ge0 (C : cell -> bool) (oram : oram) :
     is_oram C oram => 0 <= oram.`height.
   proof. by move/is_oram_height_gt0 => /#. qed.
end SimpleORAM.
