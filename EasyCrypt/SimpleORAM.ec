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

  op path2int (p : path) : int =
    bs2int (true :: p).

  op int2path (i : int) : path =
    drop 1 (int2bs (ceil (log2 i%r)) (i - 1)).

  op K: int.
  (* we need K %/ 2 - 1 >= 0 *)
  axiom K_ge2 : 2 <= K.

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
    var overflow : path -> bool

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
        overflow <- overflow.[[] <- true];
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
          overflow <- overflow.[ps <- true];
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

    proc owrite(oram : oram, c : cell, v : value) : oram * value = {
      var block : block;
      var pos  : path;
      var tmpo : oram option;
      var aout : (oram * value option) option;

      (oram, block) <@ fetch(oram, c);
      pos  <$ dlist {0,1} oram.`height;
      oram <- {| oram with positions = oram.`positions.[c <- pos] |};
      oram <@ putback(oram, (c, pos, v));
      oram <@ flush(oram);

      return (oram, v);
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
        | Wt t => { (o, v) <@ owrite(o, t.`1, t.`2); os <- v :: os; }
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

  (* -------------------------------------------------------------------- *)
  type soram = {
    sheight : int;
    smap    : cell -> path * value;
  }.

  type sleakage = [
  | Fetch   of path
  | Flush   of path
  | Putback
  ].

  module SimpleORAM = {
    var leakage : sleakage list

    proc fetch(oram : soram, c : cell) : soram * block = {
      var b <- oram.`smap c;

      leakage <- Fetch b.`1 :: leakage;
      return (oram, (c, b.`1, b.`2));
    }

    proc putback(oram : soram, b : block) : soram = {
      oram <- {| oram with smap = oram.`smap.[b.`1 <- (b.`2, b.`3)] |};
      leakage <- Putback :: leakage;
      return oram;
    }

    proc flush(oram : soram) : soram = {
      var p : path;

      p       <$ dlist {0,1} oram.`sheight;
      leakage <- Flush p :: leakage;

      return oram;
    }

    proc oread(oram : soram, c : cell) : soram * value = {
      var block : block;
      var pos  : path;

      (oram, block) <@ fetch(oram, c);
      pos  <$ dlist {0,1} oram.`sheight;
      oram <@ putback(oram, (block.`1, pos, block.`3));
      oram <@ flush(oram);

      return (oram, block.`3);
    }

    proc owrite(oram : soram, c : cell, v : value) : soram * value = {
      var block : block;
      var pos  : path;
      var tmpo : oram option;
      var aout : (oram * value option) option;

      (oram, block) <@ fetch(oram, c);
      pos  <$ dlist {0,1} oram.`sheight;
      oram <@ putback(oram, (c, pos, v));
      oram <@ flush(oram);

      return (oram, v);
    }

    proc compile(o : soram, p : prog) : soram * (value list) = {
      var i : int;
      var v : value;
      var os : value list;
      os <- [];
      i <- 0;
      while (i < size p) {
        match (nth witness p i) with
        | Rd c => { (o, v) <@ oread(o, c); os <- v :: os; }
        | Wt t => { (o, v) <@ owrite(o, t.`1, t.`2); os <- v :: os; }
        end;
        i <- i + 1;
      }
      return (o, os);
    }
  }.

  op is_soram (o : soram) =
    0 < o.`sheight && (forall c, size (o.`smap c).`1 = o.`sheight).

  op leakages_of_sleakage (h : int) (l : sleakage) : leakage list =
    with l = Fetch p => flatten (map (fun i => [(Write, take i p); (Read, take i p)]) (rev (range 0 (h+1))))
    with l = Flush p => flatten (map (fun i => [(Write, take i p); (Read, take i p)]) (rev (range 0 (h+1))))
    with l = Putback => [(Write, [])].

  op leakages_of_sleakages (h : int) (l : sleakage list) : leakage list =
    flatten (map (leakages_of_sleakage h) l).

  abbrev leakage_rel (h : int) (l : leakage list) (sl : sleakage list) =
    (leakages_of_sleakages h sl = l).
   
  op oram_rel (_C : cell -> bool) (_h : int) (_oram : oram) (_soram : soram) =
       _oram.`height = _h
    && _soram.`sheight = _h
    (* all the positions are the same *)
    && (forall c, _C c => _oram.`positions c = (_soram.`smap c).`1)
    (* all the values are the same *)
    && (forall p, size p <= _oram.`height =>
          let block = _oram.`bucket p in
          forall b, b \in block => (_C b.`1) => b.`3 = (_soram.`smap b.`1).`2)
    && is_oram _C _oram
    && is_soram _soram.

theory Aux.
lemma mem_trim (l : 'a list) (i : int)  (v : 'a) :
   v \in trim l i => v \in l by smt(mem_take mem_drop mem_cat).

lemma find_rng_in (l : 'a list) (P : 'a -> bool) :
   has P l <=> (0 <= find P l < size l).
split.
+ elim l => //= x l Hi H;elim H;smt(List.size_ge0).
elim l => //= x l Hi H; smt(has_find).
qed.

lemma find_rng_out (l : 'a list) (P : 'a -> bool) :
   !has P l <=> !(find P l < size l).
split.
elim l => //=;smt(List.size_ge0).
elim l => //= x l Hi H; smt(has_find).
qed.

lemma find_max (l : 'a list) (P : 'a -> bool) :
   find P l <= size l.
elim l => //=;smt(find_ge0).
qed.

lemma trim_cons_false (l : 'a list) (x : 'a) (P : 'a -> bool) :
   !P x => trim (x :: l) (find P (x :: l)) = x :: trim l (find P l).
proof.
move => Hp /=; rewrite Hp /=.
by rewrite /trim /= !ifF; 1,2:smt(find_ge0 find_rng_in find_rng_out).
qed.

lemma trim_mem (l : 'a list) (x : 'a) (P : 'a -> bool) :
    x \in l => !P x => x \in trim l (find P l) by
  elim l => //= h t /= Hi H; elim H;smt(trim_cons_false).

lemma trim_id(l : 'a list) (i : int) :
   !(0 <= i < size l) => (trim l i) = l.
case (i < 0); 1: by smt(take0 drop0).
move => ??.
by rewrite /trim take_oversize 1:/# drop_oversize 1:/# cats0.
qed.

lemma find_trim_lt (l : 'a list) (P : 'a -> bool) (i : int) :
   0 <= i < (find P l) =>  l.[i] = (trim l (find P l)).[i].
move => ?; rewrite /trim /"_.[_]" nth_cat size_take 1:/#.
by smt(nth_take find_max).
qed.

lemma find_trim_ge (l : 'a list) (P : 'a -> bool) (i : int) :
   (find P l) < i < size l =>  l.[i] = (trim l (find P l)).[i-1].
move => ?; rewrite /trim /"_.[_]" nth_cat size_take;1:smt(find_ge0).
rewrite ifF 1:/# ifT 1:/# nth_drop;smt(find_ge0).
qed.

lemma uniq_take (l : 'a list) (n : int) : uniq l => uniq (take n l).
proof. by rewrite -{1}[l](cat_take_drop n) cat_uniq. qed.

lemma uniq_cells  (_oram : oram) (_p  : path) (_i : int) :
  (forall (p1 p2 : path),
          let bucket1 = _oram.`bucket p1 in
          let bucket2 = _oram.`bucket p2 in
           forall i1 i2, 0 <= i1 < size bucket1 => 0 <= i2 < size bucket2 =>
             let bucket1 = bucket1.[i1] in
             let bucket2 = bucket2.[i2] in
             bucket1.`1 = bucket2.`1 => p1 = p2 /\ i1 = i2) =>
  size _p = _oram.`height =>
  0 <= _i <= _oram.`height =>
   uniq (map (fun (b : block) => b.`1) (_oram.`bucket (take _i _p))).
proof.
rewrite /is_oram => /> *; apply nth_uniq => i j *.
by rewrite !(nth_map witness) /=;smt(List.size_map).
qed.

lemma mem_uniq_triple (l : ('a * 'b * 'c) list) (v : 'a) :
     uniq (map (fun (x : ('a * 'b * 'c)) => x.`1) l)
  => !has
        (fun  (x : ('a * 'b * 'c)) => x.`1 = v)
        (trim l (find (fun  (x : ('a * 'b * 'c)) => x.`1 = v) l)).
proof.
elim l => //= x k; rewrite !hasP !negb_exists /=.
by move=> Hi [H1 H2]; smt(uniq_map).
qed.

lemma find_cat_out (s1 s2 : 'a list) (P : 'a -> bool) :
     (size (s1 ++ s2) <= find P (s1 ++ s2))
 <=> (size s1 <= find P s1 /\ size s2 <= find P s2).
proof. by rewrite !lezNgt /= -!find_rng_out has_cat /#. qed.

lemma block_props (_C : cell -> bool) (_oram) (b : block) (_p : path) :
    is_oram _C _oram => size _p <= _oram.`height => b \in _oram.`bucket _p =>
      _C b.`1 => (_oram.`positions b.`1 = b.`2 /\
              take (size _p) b.`2 = _p).
proof.
auto => />? H H0 H1 H2 H3 H4 H5 H6;smt(take_size).
qed.

lemma filter_inj (l : 'a list) (F : 'a -> 'b) (P : 'a -> bool) :
    (forall i1 i2,
    0 <= i1 < size l =>
    0 <= i2 < size l =>
    (F (nth witness l i1) = F (nth witness l i2) => i1 = i2)) =>
    (forall i1 i2,
    0 <= i1 < size (filter P l) =>
    0 <= i2 < size (filter P l) =>
    (F (nth witness (filter P l) i1) = F (nth witness (filter P l) i2) => i1 = i2)).
proof.
    move => H i1 i2 Hi1 H12 HF.
    have ? : uniq l by apply nth_uniq; smt().
    have ? : uniq  (filter P l) by apply filter_uniq; smt().
    have H2 : forall x1 x2, x1 \in l => x2\in l => F x1 = F x2 => x1 = x2 by smt(nth_uniq).
    have H3 : forall x1 x2, x1 \in (filter P l) => x2\in (filter P l) => F x1 = F x2 => x1 = x2
      by  move => x1 x2; rewrite !mem_filter /#.
    pose ii1 := index  (nth witness (filter P l) i1) (filter P l).
    pose ii2 := index  (nth witness (filter P l) i2) (filter P l).
    pose if1 := index  (nth witness (filter P l) i1) l.
    pose if2 := index  (nth witness (filter P l) i2) l.
    have ? : if1 = if2 by smt( mem_nth).
    by smt(index_uniq mem_nth).
qed.

end Aux.
export Aux.

 op is_oram_fetch (C : cell -> bool) (_c : cell) (o : oram) =
       (* we have at least two levels *)
       0 < o.`height

       (* There is nothing below the leafs *)
    && (forall (p : path), o.`height < size p => o.`bucket p = [])

       (* Well formness of the positions map: all paths of correct size *)
    && (forall (p : path), (exists c, p = o.`positions c) => size p = o.`height)

       (* only cells in the map are on the tree *)
    && (forall (p : path), size p <= o.`height =>
          (forall block, block \in o.`bucket p =>
              block.`1 <> _c => (C block.`1)))

       (* Path invariant: there exists a block holding the cell in the path
          to its position *)
    && (forall (c : cell), (predI C (predC1 _c)) c =>
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

  op oram_rel_fetch (_C : cell -> bool) (_c : cell) (_h : int) (_oram : oram) (_soram : soram) =
       _oram.`height = _h
    && _soram.`sheight = _h
    (* all the positions are the same *)
    && (forall c, _C c => _oram.`positions c = (_soram.`smap c).`1)
    (* all the values are the same *)
    && (forall p, size p <= _oram.`height =>
          let block = _oram.`bucket p in
          forall b, b \in block => (_C b.`1) => b.`3 = (_soram.`smap b.`1).`2)
    && is_oram_fetch _C _c _oram
    && is_soram _soram.

   lemma is_oram_is_oram_fetch (C : cell -> bool) (o : oram) (c0 : cell) :
       is_oram C o => is_oram_fetch C c0 o.
   proof.
   rewrite /is_oram /is_oram_fetch => /> *; do! split.
   + move => p ? block * /#.
   + move => ? c * /#.
   qed.

  lemma is_oram_is_oram_putback (C : cell -> bool) (o : oram) (b : block) :
      is_oram C o
   => !C b.`1
   => o.`positions b.`1 = b.`2
   => is_oram (predU C (pred1 b.`1))
        {| height = o.`height; bucket = o.`bucket.[[] <- o.`bucket [] ++ [b]]; positions = o.`positions; |}.
  proof.
  move => /> //= ???? He ? Hf *; do! split.
    - smt().
    - move => *; split; 1: smt(mem_cat).
    - move => *; split.
      move => c.
      case: (c = b.`1) => *.
      + exists 0 => //=.
        split => *; 1: by smt().
        rewrite take0 /"_.[_<-_]" //= has_cat; right.
        rewrite hasP.
        exists b => //= /#.
      + move : (He c _); 1: smt().
        move => Hec; elim Hec => i Hi; exists i => * /=.
        by rewrite hasP in Hi; rewrite hasP; smt(mem_cat).
    + move => Hc; split.
      + move => p1 p2 i1 i2.
      case (p1 = []); case (p2 = []); 4:smt().
      + move => -> -> /=; rewrite /"_.[_<-_]" /= !size_cat /= /"_.[_]" /= !nth_cat /=.
        case (i1 = size (o.`bucket []));case (i2 = size (o.`bucket [])); 1,4:smt().
        + move => ??????; rewrite ifF 1:/# ifT 1:/# ifT 1:/#.
          by smt(size_nseq mem_nth).
        + move => ??????; rewrite ifT 1:/# ifF 1:/# ifT 1:/#.
          by smt(size_nseq mem_nth).
      + move => ? -> /=; rewrite /"_.[_<-_]" /= !size_cat /= /"_.[_]" /= !nth_cat /=.
        case (i1 = size (o.`bucket []));2:smt().
        + move => ?????; rewrite ifF 1:/# ifT 1:/# ifF 1:/#.
          by smt(List.size_ge0 size_cat size_nseq mem_nth).
      + move => -> ? /=; rewrite /"_.[_<-_]" /= !size_cat /= /"_.[_]" /= !nth_cat /=.
        case (i2 = size (o.`bucket []));2:smt().
        + move => ?????; rewrite ifF 1:/# ifF 1:/# ifT 1:/#.
          by smt(List.size_ge0 size_cat size_nseq mem_nth).
    + move => ? p ? i ?? _b;rewrite /"_.[_<-_]" /=.
      case (p = [] \/ i <= 0).
      + move => ?; rewrite ifT 1:/# /= mem_cat /= => H; elim H.
        + move => *; move : (Hf p _ 0 _ _b _);smt().
        + by move => Hb; smt(take0 List.size_ge0).
      + by move => ?; rewrite ifF; smt().
  qed.

  lemma is_oram_bbpp (C : cell -> bool) (o : oram) (bb1 bb2 : block) (p1 p2 : path) :
      is_oram C o
   => bb1 \in o.`bucket p1
   => bb2 \in o.`bucket p2
   => bb1.`1 = bb2.`1
   => p1 = p2.
  proof.
  move => /> @/"_.[_]" 5? H ? Hb1 Hb2 *.
  rewrite (nthP witness) in Hb1; elim Hb1 => i1 [#] *.
  rewrite (nthP witness) in Hb2; elim Hb2 => i2 [#] *.
  by have := H p1 p2 i1 i2 _ _ _; smt().
  qed.

  lemma case_elim p q: ((p => q) /\ (!p => q)) <=> q.
  proof. by smt(). qed.
  lemma is_oram_is_oram_flush (C : cell -> bool) (oram : oram) (o : oram) (i : int) (p : path) (pushed : block list) :
      let stayhere: block list =
          if i = oram.`height then
            pushed ++ oram.`bucket (take i p)
          else
            filter
              (fun (block : block) =>
                 take (i + 1) block.`2 <> take (i + 1) p)
              (pushed ++ oram.`bucket (take i p)) in
      let newpushed: block list =
          if i = oram.`height then []
          else
            filter
              (fun (block : block) =>
                 take (i + 1) block.`2 = take (i + 1) p)
              (pushed ++ oram.`bucket (take i p)) in
      0 <= i <= oram.`height
   => is_oram C o
   => is_oram (predI C (fun cc => size pushed <= find (fun (b : block) => b.`1 = cc) pushed)) oram

   => size p = oram.`height
   => oram.`height = o.`height
   => oram.`positions = o.`positions

     (* block is in pushed iff it was higher up in the path of o, agress on the flushing path p, and it's not in the higher path of the current oram *)
   => (forall bb, bb \in pushed <=>
             (i <= o.`height
           /\ take i bb.`2 = take i p
           /\ (exists ii, 0 <= ii < i /\ bb \in o.`bucket (take ii p))))
     (* we have no repeats in pushed *)
   => (forall i1 i2,
             0 <= i1 < size pushed
           => 0 <= i2 < size pushed
           => pushed.[i1].`1 = pushed.[i2].`1
           => i1 = i2)
     (* Whatever is in current oram first levels is not in pushed and it was somewhere above in the original o *)
   => (forall _p, size _p < i =>
          (all (fun (block : block) =>
            !block \in pushed /\
             (exists ii, 0<= ii <= size _p /\ block \in o.`bucket (take ii _p))) (oram.`bucket _p)))
     (* Whatever is in current oram later levels is untouched from o *)
   => (forall _p, i <= size _p <= oram.`height => oram.`bucket _p = o.`bucket _p)
   => is_oram (predI C (fun cc => size newpushed <= find (fun (b : block) => b.`1 = cc) newpushed))
        {| height = oram.`height; bucket =
            oram.`bucket.[take i p <- stayhere]; positions =
            oram.`positions; |}.
  proof.
  move => stayhere newpushed ? ^? /> 4? Hbase Hinjb Hps ???? H0 ? H01 3? H3 H4 H1 H2 *.

  (* setting the ground *)
  have ? : forall b, (!b \in newpushed /\ !b \in stayhere) => !b \in pushed.
  + case (i = oram.`height); 1: by smt(mem_cat).
    by rewrite /newpushed /stayhere => ->b /=; rewrite !mem_filter !mem_cat /#.

  have ? : forall b, b \in stayhere => !b \in pushed => b \in oram.`bucket (take i p).
  + rewrite /stayhere;case (i = oram.`height) => ?/=;1: by smt(mem_cat).
     by move => b;rewrite !mem_filter !mem_cat /#.

  have H_newpushed_not_pushed : forall b, b \in newpushed => !b \in pushed => b \in oram.`bucket (take i p).
  + rewrite /newpushed;case (i = oram.`height) => ?/=;1: by smt(mem_cat).
     by move => b;rewrite !mem_filter !mem_cat /#.

  have ? : forall b, b \in stayhere => !b \in newpushed.
  + rewrite /stayhere /newpushed;case (i = oram.`height) => ?/=;1: by smt(mem_cat).
     by move => b;rewrite !mem_filter !mem_cat /#.

  have ? : forall b, !b \in stayhere => !b \in newpushed => !b \in oram.`bucket (take i p).
  + rewrite /stayhere /newpushed;case (i = oram.`height) => ?/=;1: by smt(mem_cat).
     by move => b;rewrite !mem_filter !mem_cat /#.

  have ?: forall bb1 bb2, bb1 \in stayhere => bb2 \in newpushed => bb1.`2 <> bb2.`2.
  + rewrite /stayhere /newpushed => bb1 bb2.
    case (i = oram.`height) => ? //.
    by rewrite !mem_filter //= /#.

  have Hsep : forall bb pp, size pp <= oram.`height =>
       bb \in oram.`bucket.[take i p <- stayhere] pp =>
        size newpushed <= find (fun (b : block) => b.`1 = bb.`1) newpushed.
  + move => bb pp ??.
    have [ _ Hin]  := find_rng_in newpushed (fun (b : block) => b.`1 = bb.`1).
    rewrite implybE in Hin;elim Hin;1: by smt(find_ge0).
    rewrite hasP=> Hex;elim Hex => b2 /= *.
    case (b2 \in stayhere) => *; 1: by smt().
    case (i < size pp) => *.  (* block is below *)
     + have ? : bb \in o.`bucket pp by smt(size_take).
       pose i1 := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket pp).
       have i1b := find_rng_in (o.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
       case (b2 \in pushed) => Hb2.
         + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
           pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i2' p)).
           have := Hinjb (take i2' p) pp i2f i1 _ _ _;2,4:smt(size_take nth_find mem_nth).
           + have := (find_rng_in (o.`bucket (take i2' p)) (fun (bf : block) => bf.`1 = b2.`1));1: by rewrite hasP; smt().
           have /= := nth_find witness (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i2' p)) _.
           + rewrite ? ha /= hasP.
             exists b2.
             by smt().
           have /= := nth_find witness (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _.
           + rewrite ? ha /= hasP.
             exists bb.
             by smt().
           by smt().
       have ? : b2 \in o.`bucket (take i p).
       + have ? : b2 \in oram.`bucket (take i p) by smt().
         by smt(size_take).
       pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i p)).
       have := Hinjb (take i p) pp i2f i1 _ _ _.
       + have := find_rng_in (o.`bucket (take i p)) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
       + smt().
       + have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i p)) _;1: by rewrite hasP /=; smt().
         have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _; by rewrite ?hasP /=; smt().
       smt(size_take).

     case (size pp < i) => *.
     (* block is above *)
     + have ? : pp <> take i p by smt(size_take).
       move : (H1 pp _); 1: by smt().
       rewrite allP => /> Hbs; move : (Hbs bb _);1:smt().
       move =>  [#? Hex];elim Hex => i1' *.
       have ? : bb \in o.`bucket (take i1' pp) by smt().
       pose i1f := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket (take i1' pp)).
       case (b2 \in pushed) => Hb2.
         + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
           pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i2' p)).
           have := Hinjb (take i2' p) (take i1' pp) i2f i1f _ _ _; 4:  by smt().
           + have := find_rng_in (o.`bucket (take i2' p)) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
           + have := find_rng_in (o.`bucket (take i1' pp)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
           + have /= ? := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i2' p)) _; 1: by rewrite ?hasP /#.
             rewrite /"_.[_]" &(eq_trans _ bb.`1).
             + smt().
             + rewrite /i1f &(eq_sym_imp).
               apply (nth_find witness (fun (b0 : block) => b0.`1 = bb.`1) (o.`bucket (take i1' pp))).
               apply List.hasP.
               by exists bb => //=.

         + have ? : b2 \in o.`bucket (take i p) by smt(size_take).
           pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i p)).
           have := Hinjb (take i p) (take i1' pp) i2f i1f _ _ _;4:smt(size_take).
           + have := find_rng_in (o.`bucket (take i p)) (fun (bf : block) => bf.`1 = b2.`1); 1: by rewrite hasP /#.
           + have := find_rng_in (o.`bucket (take i1' pp)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
           + have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i p)) _;1: by rewrite ?hasP;smt(nth_find).
           have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket (take i1' pp)) _; by rewrite ?hasP /=; smt().

     + (* block is at this level *)
       case (pp = take i p) => *; last first.
       + have Hinn : bb \in o.`bucket pp by smt().
       pose i1 := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket pp).
       have i1b := find_rng_in (o.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
       case (b2 \in pushed) => Hb2.
         + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
           pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i2' p)).
           have := Hinjb (take i2' p) pp i2f i1 _ _ _;2,4:smt(size_take).
           + have := find_rng_in (o.`bucket (take i2' p)) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
           have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i2' p)) _;1: by rewrite ?hasP;smt(nth_find).
           have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _; by rewrite ?hasP /=; smt().

         have ? : b2 \in o.`bucket (take i p) by smt(size_take).
         pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i p)).
         have := Hinjb (take i p) pp i2f i1 _ _ _;2,4:smt(size_take).
         + have := find_rng_in (o.`bucket (take i p)) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
         + have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i p)) _;1: by rewrite ?hasP /=; smt().
         have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _; by rewrite ?hasP /=; smt().

     + have ? : bb \in stayhere;1: by smt().
       case (bb \in pushed) => Hpps;last first.
       +  have ? : bb \in (o.`bucket pp) by smt().
          pose i1 := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket pp).
          have i1b := find_rng_in (o.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
          case (b2 \in pushed) => Hb2.
           + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
             pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i2' p)).
             have := Hinjb (take i2' p) pp i2f i1 _ _ _;2,4:smt().
             + have := find_rng_in (o.`bucket (take i2' p)) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
             have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i2' p)) _;1: by rewrite ?hasP /=; smt().
           have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _; by rewrite ?hasP /=; smt().

          have ? : b2 \in o.`bucket (take i p) by smt().
          pose i2f := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket (take i p)).
          have := Hinjb (take i p) pp i2f i1 _ _ _; 2, 4: smt().
          + by have := find_rng_in (o.`bucket (take i p)) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
          + by have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i p)) _; by rewrite ?hasP /=; smt().

          case (b2 \in pushed) => Hb2.
           + pose i1f := find (pred1 bb) pushed.
             pose i2f := find (pred1 b2) pushed.
             move : (H4 i1f i2f) ; smt().

          move : (H3 bb);rewrite Hpps /= => [#?? Hex];elim Hex => i1' *.
          pose i1f := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket (take i1' p)).
          have ? : b2 \in o.`bucket (take i p) by smt().
          pose i2f := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket (take i p)).
          have := Hinjb (take i p) (take i1' p) i2f i1f _ _ _;3..:smt().
          + have := find_rng_in (o.`bucket (take i p)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
          + have := find_rng_in (o.`bucket (take i1' p)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().

    have Hinjf : forall bb1 bb2 pp1 pp2, bb1 \in o.`bucket pp1 => bb2 \in o.`bucket pp2 =>
              bb1.`1 = bb2.`1 => pp1 <> pp2 => false.
      move => bb1 bb2 pp1 pp2 Hl1 Hl2 Hl3 Hl4.
      pose i1f := find (fun (bf : block) => bf.`1 = bb1.`1) (o.`bucket pp1).
      pose i2f := find (fun (bf : block) => bf.`1 = bb2.`1) (o.`bucket pp2).
      have := Hinjb pp1 pp2 i1f i2f _ _ _.
           + have := find_rng_in (o.`bucket pp1) (fun (bf : block) => bf.`1 = bb1.`1); rewrite hasP; smt().
           + have := find_rng_in (o.`bucket pp2) (fun (bf : block) => bf.`1 = bb2.`1); rewrite hasP; smt().
             have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb1.`1)(o.`bucket pp1)_;1: by rewrite ?hasP /=; smt().
           have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb2.`1) (o.`bucket pp2)  _; by rewrite ?hasP /=; smt().
           by smt(size_take).

     (* pushed{hr} + bucket (take i{hr} p{m}) = stayhere + newpushed *)
     have ?: forall b, (b \in pushed \/ b \in (oram.`bucket (take i p))) <=> (b \in stayhere \/ b \in newpushed).
     + smt().

     (* pushed{hr} /\ bucket (take i p) = \emptyset *)
    have Hpushed: forall b1 b2 p0, (i <= size p0 <= oram.`height) => (b1 \in pushed) => b2 \in (oram.`bucket p0) => b1.`1 <> b2.`1.
     + move => b1 b2 p0 ? Hb1 Hb2.
       move: Hb1.
       rewrite H3 => /> ?? ii *.
       have Hbb2: b2 \in o.`bucket p0 by smt().
       apply negP => ?.
       have ? : take ii p = p0.
       + apply (is_oram_bbpp C o b1 b2 (take ii p) p0) => //=.
       by smt(size_take).

     (* stayhere /\ newpushed = \emptyset *)
     have ?: forall b, (b \in stayhere) => !(b \in newpushed).
     + smt().

     + move=> *; split.
       + move => //= @/"_.[_<-_]" p0 ?.
         have -> /=: !take i p = p0 by smt(size_take).
         by smt().
       move=> /> *; split.
       + move => pp ? bb Hbb; split;1: by
         case (i < size pp) => *;
         case (size pp < i) => *;smt().
       (* it remains to show not in newpushed *)
       by exact (Hsep bb pp).

       move=> /> *; split.
       + move => c Hc Hnh.
         case (size stayhere <= find (fun (b : block) => b.`1 = c) stayhere) => Hcs; last first.
         + (* storing it now: it's in stayhere *)
           exists i; split => *; 1: smt().
           have  := find_rng_in stayhere (fun (b : block) => b.`1 = c). (* Question. *)
           have -> /= : 0 <= find (fun (b : block) => b.`1 = c) stayhere < size stayhere
                by smt(List.size_ge0 find_ge0).
           rewrite hasP => Hex; elim Hex => bb *.
           rewrite hasP; exists bb.
           by case (bb \in pushed) => Hip; by move : (Hps p _ i _);smt().
          + (* already in tree *)
            move : (H0 c _).
            + rewrite /predI /=;split;1:smt().
              have  := find_rng_out stayhere (fun (b : block) => b.`1 = c).
              have  := find_rng_out newpushed (fun (b : block) => b.`1 = c).
              have  := find_rng_out pushed (fun (b : block) => b.`1 = c).
              rewrite !hasP !negb_exists //=.
              smt().
            move => H0c; elim H0c => i' [#?? Hb]; exists i';do split;1,2:smt().
            rewrite hasP in Hb; elim Hb => bb /= *.
            rewrite hasP; exists bb => /=.
            case (i' < i) => *; 1: by smt(size_take). (* block is below *)
            case (i = i') => *; last by smt(size_take).
            + have ? : take i p <> (take i' (oram.`positions c)); last by smt().
              have  := find_rng_out stayhere (fun (b : block) => b.`1 = c).
              have  := find_rng_out newpushed (fun (b : block) => b.`1 = c).
              have  := find_rng_out (oram.`bucket (take (i) p)) (fun (b : block) => b.`1 = c).
              rewrite !hasP !negb_exists /=.
              have -> /= : ! find (fun (b : block) => b.`1 = c) newpushed < size newpushed by smt().
              have -> /= : ! find (fun (b : block) => b.`1 = c) stayhere < size stayhere by smt().
              move => Hib Hinp Hish; move : (Hinp bb); move : (Hish bb); rewrite  (: bb.`1 = c) 1:/# /=.
              by smt().

       + move => /> *; split.
         move => /> p1 p2 i1 i2 ????.
         (* begin injectivity *)
         rewrite /"_.[_<-_]".
         case (take i p = p1);
         case (take i p = p2) => ??; last by smt().
         + rewrite /stayhere; case (i = oram.`height) => ?.
           + rewrite /"_.[_]" !nth_cat.
             case (i1 < size pushed); case (i2 < size pushed) => ??;1,4 : smt(size_cat size_filter List.size_ge0).
             + move => ?; pose b1 := nth witness pushed i1.
               pose b2 := nth witness (oram.`bucket (take i p)) (i2 - size pushed).
               have Hb1 : b1 \in pushed by smt(mem_nth).
               have Hb2 : b2 \in (oram.`bucket (take i p)) by smt(size_filter size_cat List.size_ge0 mem_nth).
               have ? := Hpushed b1 b2 (take i p) _ _ _; 2,3: by assumption.
               + by smt(size_take).
               by smt().
               (* by smt(size_take) *)
             + move => ?; pose b2 := nth witness pushed i2.
               pose b1 := nth witness (oram.`bucket (take i p)) (i1 - size pushed).
               have Hb2 : b2 \in pushed by smt(mem_nth).
               have Hb1 : b1 \in (oram.`bucket (take i p)) by smt(size_filter size_cat List.size_ge0 mem_nth).
               have ? := Hpushed b2 b1 (take i p) _ _ _; 2,3: by assumption.
               + by smt(size_take).
               by smt().

           + have /= HH := (filter_inj
                   (pushed ++ oram.`bucket (take i p))
                   (fun (b : block) => b.`1)
                   (fun (block : block) => take (i + 1) block.`2 <> take (i + 1) p)).
             have ? : (forall (i1 i2 : int),
               0 <= i1 < size (pushed ++ oram.`bucket (take i p)) =>
               0 <= i2 < size (pushed ++ oram.`bucket (take i p)) =>
                  (nth witness (pushed ++ oram.`bucket (take i p)) i1).`1 =
                  (nth witness (pushed ++ oram.`bucket (take i p)) i2).`1 =>
                     i1 = i2) ; last by smt().
             move => ii1 ii2 ??.
             rewrite /"_.[_]" !nth_cat.
             case (ii1 < size pushed); case (ii2 < size pushed) => ??;1,4:smt(size_cat size_filter List.size_ge0).
             + move => ?; pose b1 := nth witness pushed ii1.
               pose b2 := nth witness (oram.`bucket (take i p)) (ii2 - size pushed).
               have Hb1 : b1 \in pushed by smt(mem_nth).
               have Hb2 : b2 \in (oram.`bucket (take i p)) by smt(mem_nth size_cat size_filter List.size_ge0).
               have ? := Hpushed b1 b2 (take i p) _ _ _; 2,3: by assumption.
               + by smt(size_take).
               by smt().

             + move => ?; pose b2 := nth witness pushed ii2.
               pose b1 := nth witness (oram.`bucket (take i p)) (ii1 - size pushed).
               have Hb2 : b2 \in pushed by smt(mem_nth).
               have Hb1 : b1 \in (oram.`bucket (take i p)) by smt(size_filter size_cat List.size_ge0 mem_nth).
               have ? := Hpushed b2 b1 (take i p) _ _ _; 2,3: by assumption.
               + by smt(size_take).
               by smt().

         + pose b1 := stayhere.[i1].
           pose b2 := (oram.`bucket p2).[i2].
           move => ?.
           have Hb2 : b2 \in oram.`bucket p2 by smt(mem_nth).
           have  : b1 \in stayhere by smt(mem_nth).
           rewrite /stayhere => ?.
           case (b1 \in pushed) => Hb1.
          + have := H3 b1; rewrite Hb1 /= => [#?? Hex];elim Hex => i1' *.
            case (i < size p2) => *.
            + have ? : b2 \in o.`bucket p2 by smt(mem_nth).
              have ? := Hpushed b1 b2 p2 _ _ _; 2,3: by assumption.
              + by smt(size_take).
              by smt().

            case (i = size p2) => *.
            + have ? : b2 \in o.`bucket p2 by smt(mem_nth).
              have ? := Hpushed b1 b2 p2 _ _ _; 2,3: by assumption.
              + by smt(size_take).
              by smt().

            + have := H1 p2 _;1:smt().
              rewrite allP => H1p2; move : (H1p2 b2 _) => /=;1:smt().
              move => [# H_b2_pushed Hex];elim Hex => i2' *.
              have Hbb2: take i b2.`2 <> take i p.
              + apply negP => ?.
                move: H_b2_pushed.
                rewrite H3 => //=.
                have -> /=: i <= o.`height by assumption.
                split; 1: by assumption.
                exists i2'.
                by smt(take_take).
              by smt().

           + have Hbb1 : b1 \in o.`bucket (take i p) by smt(size_take).
             case (i < size p2) => *.
             + have Hbb2 : b2 \in o.`bucket p2 by smt(mem_nth).
               have ?: (take i p) = p2.
               + apply (is_oram_bbpp C o b1 b2 (take i p) p2); by assumption.
               by smt(size_take).
             case (i = size p2) => *.
             + have Hbb2 : b2 \in o.`bucket p2 by smt(mem_nth).
               have ?: (take i p) = p2.
               + apply (is_oram_bbpp C o b1 b2 (take i p) p2); by assumption.
               by smt(size_take).
             + have := H1 p2 _;1:smt().
               rewrite allP => H1p2; move : (H1p2 b2 _) => /=;1:smt().
               move => [#? Hex];elim Hex => i2' *.
               have ?: (take i p) = (take i2' p2).
               + apply (is_oram_bbpp C o b1 b2 (take i p) (take i2' p2)) => //= /#.
               by smt(size_take).

         + pose b2 := stayhere.[i2].
           pose b1 := (oram.`bucket p1).[i1].
           move => ?.
           have Hb1 : b1 \in oram.`bucket p1 by smt(mem_nth).
           have  : b2 \in stayhere by smt(mem_nth).
           rewrite /stayhere => ?.
           case (b2 \in pushed) => Hb2.
           + have := H3 b2; rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
             case (i < size p1) => *.
             + have ? : b1 \in o.`bucket p1 by smt(mem_nth).
               have ?: p1 = take i2' p.
               + apply (is_oram_bbpp C o b1 b2 p1 (take i2' p)) => //= /#.
               by smt(size_take).
             case (i = size p1) => *.
             + have ? : b1 \in o.`bucket p1 by smt(mem_nth).
               have ? : p1 = take i2' p.
               + apply (is_oram_bbpp C o b1 b2 p1 (take i2' p)) => //= /#.
               by smt(size_take).
             + have := H1 p1 _;1:smt().
               rewrite allP => H1p1; move : (H1p1 b1 _) => /=;1:smt().
               move => [# H_b1_pushed Hex];elim Hex => i1' *.
               have ?: take i b1.`2 <> take i p.
               + apply negP => ?.
                 move: H_b1_pushed.
                 rewrite H3 => //=.
                 have -> /=: i <= o.`height by assumption.
                 split; 1: by assumption.
                 exists i1'.
                 rewrite (_: take i1' p = take i1' (take i p)); 1: by smt(take_take).
                 rewrite (_: take i p = take i b1.`2); 1: by smt().
                 rewrite (_: take i1' (take i b1.`2) = take i1' b1.`2); 1: by smt(take_take).
                 have := Hps p1 _ i1' _ b1 _; by smt().
               by smt().
           + have Hbb2 : b2 \in o.`bucket (take i p) by smt(size_take).
             case (i < size p1) => *.
             + have Hbb1 : b1 \in o.`bucket p1 by smt(mem_nth).
               have ? : p1 = take i p.
               + apply (is_oram_bbpp C o b1 b2 p1 (take i p)) => //= /#.
               by smt().
             case (i = size p1) => *.
             + have Hbb1 : b1 \in o.`bucket p1 by smt(size_take).
               have ? : p1 = take i p.
               + apply (is_oram_bbpp C o b1 b2 p1 (take i p)) => //= /#.
               by smt(size_take).
             + have := H1 p1 _;1:smt().
               rewrite allP => H1p1; move : (H1p1 b1 _) => /=;1:smt().
               move => [#? Hex];elim Hex => i1' *.
               have ?: (take i1' p1) = take i p.
               + apply (is_oram_bbpp C o b1 b2 (take i1' p1) (take i p)) => //= /#.
               by smt(size_take).
       (* end injectivity*)

       + move => ? pp Hpp ii ?? bb Hbb.
         case (size (take ii pp) <= i) => *; last first.
         + (* bb is below *)
           have ?: bb \in oram.`bucket (take ii pp) by smt(size_take).
           move : (H2 (take ii pp) _); 1:smt().
           move : (Hps pp _ ii _); smt(size_take).
         case (size (take ii pp) < i) => *.
         + (* bb is above *)
           have ?: bb \in oram.`bucket (take ii pp) by smt(size_take).
           move : (H01 pp _ ii _ bb _); smt(size_take).
         (* bb is at level i *)
         case (take i p = take i pp) => *; last first.
         + (* other path *)
           have ?: bb \in o.`bucket (take ii pp);  by smt(take_oversize size_take).
           move : (Hps pp _ ii _);smt(size_take).
  qed.

lemma equiv_fetch (_C : cell -> bool) (_oram : oram) (_soram : soram) (_c : cell) (_h : int) :
    equiv[ORAM.fetch ~ SimpleORAM.fetch :
         arg{1} = (_oram, _c)
      /\ arg{2} = (_soram, _c)
      /\ _oram.`positions _c = (_soram.`smap _c).`1
      /\ oram_rel _C _h _oram _soram
      /\ leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2}
    ==>
          res{1}.`1.`positions = _oram.`positions
      /\  res{2}.`1 = _soram
      /\  (oram_rel (predI _C (predC1 _c)) _h res{1}.`1 res{2}.`1)
      /\  (forall p i, 0 <= i <= res{1}.`1.`height =>
                           size p = res{1}.`1.`height =>
                let block = res{1}.`1.`bucket (take i p) in
                 !(has (fun (block : block) => block.`1 = _c) block))
      /\ (_C _c => (res{1}.`2 = res{2}.`2 /\ res{2}.`2.`1 = _c))
      /\ leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2}
  ].
  proof.
  proc => /=; sp; elim* => _sl2.
  exists* ORAM.leakage{1}; elim* => _l1.
  while {1} (0 <= i{1} <= _h + 1
    /\ pos{1} = b{2}.`1
    /\ ={c}
    /\ c{2} = _c
    /\ pos{1} = oram{1}.`positions c{1}
    /\ oram{1}.`positions = _oram.`positions
    /\ oram{2} = _soram
    /\ _h = oram{1}.`height
    /\ is_oram _C _oram
    /\ _oram.`positions _c = (_soram.`smap _c).`1
    /\ oram_rel _C _h _oram _soram
    /\ oram_rel_fetch _C _c _h oram{1} oram{2}
    /\ (forall _p _i, 0 <= _i < i{1} =>
                            size _p = oram{1}.`height =>
                let block = oram{1}.`bucket (take _i _p) in
                 !(has (fun (block : block) => block.`1 = _c) block))
    /\ (forall ii pp, (i{1} <= ii <= _h => size pp = _h =>
           oram{1}.`bucket (take ii pp) = _oram.`bucket (take ii pp)))
    /\ (_C _c =>(forall ii, (0 <= ii < i{1} /\
            (has (fun (block : block) => block.`1 = _c) (_oram.`bucket (take ii pos{1}))))
          => v{1} =
               let j = find (fun (block : block) => block.`1 = _c)
                 (_oram.`bucket (take ii pos{1})) in Some (_oram.`bucket (take ii pos{1})).[j]))
    /\ (leakage_rel _h _l1 _sl2)
    /\ (leakage_rel (i{1}-1) (take (2*i{1}) ORAM.leakage{1}) [Fetch b{2}.`1])
    /\ drop (2*i{1}) ORAM.leakage{1} = _l1
    /\ SimpleORAM.leakage{2} = Fetch b{2}.`1 :: _sl2
  ) (_h + 1 - i){1}.
  + move => &2;auto => /> &1 [#] 9? Hii 22? He Hi Hf 2? H1 H H0 leakage 2? /=;do split.
    + move => * /=; do split;1,2,8..: by smt(rangeSr rev_rcons flatten_cons flatten1).
      + move => *;split;1: by smt(mem_trim).
        move => *;split;1: by smt().
        move => *;split;1: smt(mem_trim).
        move => *;split.
        + move => _c0 Hc Hnc0; elim (He _c0 _);1:smt().
          move => ip [Hip Heip]; exists ip;split;1:smt().
          move => Hipp /=;rewrite hasP in Heip;elim Heip => /= b' Hb.
          rewrite hasP => /=; exists b';split;2:smt().
          by smt(trim_mem).
        by smt(mem_trim find_trim_lt find_trim_ge size_trim trim_id).
      + move => pp ii???.
        case (ii = i{1}); 2: by smt(size_take).
        move => Hii1; rewrite Hii1 /=.
        case(take i{1} b{2}.`1 = take i{1} pp);1: by
         move => -> /=; rewrite /"_.[_<-_]" /=;apply mem_uniq_triple;apply uniq_cells => /#. 
        move => Hpp; rewrite  /"_.[_<-_]" Hpp /= H 1,2:/# hasP negb_exists /= /#.

      + by smt(size_take).

      + move => Hc ii il ih Hiii.
        have ? : ii = i{1}; last by  move : (Hi (take i{1} b{2}.`1) (take ii b{2}.`1));smt().
        pose ii1 := find (fun (x : block) => x.`1 = c{2}) (_oram.`bucket (take i{1} b{2}.`1)).
        pose ii2 := find (fun (x : block) => x.`1 = c{2}) (_oram.`bucket (take ii b{2}.`1)).
        by move : (Hii (take i{1} b{2}.`1) (take ii b{2}.`1) ii1 ii2);
              smt(nth_find find_rng_in find_rng_out find_max).
    + rewrite !ifF 1,2:/# /leakages_of_sleakages /=.
      simplify leakages_of_sleakage => /=.
      rewrite flatten1 /= rangeSr 1:/# /= rev_rcons /= flatten_cons.
      rewrite !cat_cons cat0s;do congr.
      have -> : (2 * (i{1} + 1) - 2)  = 2*i{1}  by ring.
      rewrite -leakage /leakages_of_sleakages /=.
      simplify leakages_of_sleakage => /=.
      by rewrite flatten1 /#.

  + auto => /> *;do split;1,2,4,7..:smt().
    + move => _p _i Hi1 Hi2 Hp; case (_i = i{1}); last by smt().
      move => H_i; rewrite H_i; case (_p = b{2}.`1); 1: by smt(find_rng_in).
      rewrite hasP negb_exists => Hpp be /=; smt(hasPn find_rng_in).

   + by smt(find_rng_in).

   + rewrite !ifF 1,2:/# /leakages_of_sleakages /=.
     simplify leakages_of_sleakage => /=.
     rewrite flatten1 /= rangeSr 1:/# /= rev_rcons /= flatten_cons.
     rewrite !cat_cons cat0s;do congr.
     have -> : (2 * (i{1} + 1) - 2)  = 2*i{1}  by ring.
     rewrite -leakage.
     rewrite /leakages_of_sleakages /=.
     simplify leakages_of_sleakage => /=.
     by rewrite flatten1 /#.

  auto => /> ??Hp Hv????He?Hpath??;do split;1..4,6:smt().
  + rewrite /leakages_of_sleakages take0 /=.
    simplify leakages_of_sleakage => /=.
    by rewrite range_geq //=.

  + move => l1 i1 o1 vl *; split;1: smt().
    move => 19? Hnc ?Hvv Ht Hd;do split;2:smt(). 
    move => *;do split;1:smt().
    move => *;do split;1:smt(). 
    move => ???? pp ? bb ?. 
    + have := Hnc (pp++nseq (o1.`height - size pp) false) (size pp) _ _;1,2: smt(size_cat size_nseq List.size_ge0). 
      by rewrite hasPn;smt(take_size_cat).
    move=> *;move : (He _c _);1: smt().
    move => Hee;elim Hee => kk [? H].
    rewrite (Hvv _ kk _) /=;1: smt().
    + rewrite hasP /=; rewrite hasP in H; smt().
    + pose jj := find (fun (block : block) => block.`1 = _c)
                                    (_oram.`bucket (take kk (_oram.`positions _c))).
       move : (Hv (take kk (_oram.`positions _c)) _
                 (_oram.`bucket (take kk (_oram.`positions _c))).[jj] _ _);1..3:smt(find_rng_in hasP has_nthP mem_nth).
     have ? : (_oram.`bucket (take kk (_oram.`positions _c))).[jj].`1 = _c by smt(nth_find has_nthP).
     have ? : (_oram.`bucket (take kk (_oram.`positions _c))).[jj].`2 = (_soram.`smap _c).`1.
     + rewrite -(Hp _c);move : (Hpath (_oram.`positions _c) _ kk) => /=; smt(find_rng_in has_nthP).
     by smt().

  rewrite -(cat_take_drop (2*i1) l1) Hd -Ht /leakages_of_sleakages.
  rewrite map_cons flatten_cons;congr => /=.
  simplify leakages_of_sleakage => /=.
  by rewrite !flatten1  /#.
qed.

lemma equiv_putback (_C : cell -> bool) (_oram : oram) (_soram : soram) (_b : block) (_h : int) :
    equiv[ORAM.putback ~ SimpleORAM.putback :
         arg{1} = (_oram, _b)
      /\ arg{2} = (_soram, _b)
      /\ oram_rel _C _h _oram _soram /\ !_C _b.`1
      /\  (forall p i, 0 <= i <= _oram.`height =>
                           size p = _oram.`height =>
                let bs = _oram.`bucket (take i p) in
                 !(has (fun (bb : block) => bb.`1 = _b.`1) bs))
      /\ _oram.`positions _b.`1 = _b.`2
      /\ leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2}
    ==>
         res{1}.`positions = _oram.`positions
      /\ (forall cc, cc <> _b.`1 => res{2}.`smap cc = _soram.`smap cc)
      /\ oram_rel (predU _C (pred1 _b.`1)) _h res{1} res{2}
      /\ leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2}
  ].
  proof.
  proc => /=.
  auto => /> 7? He ?Hf? ?? Hne *;split;1:smt().
  move => *;split; 1:smt().
  move => *;split.
  + move => p Hp b'.
    case (b'.`1 = _b.`1); last by smt(mem_cat).
    move => H Hin; have ? : b' = _b; last by smt().
    move : Hin; rewrite /"_.[_<-_]".
    have ? : !b' \in _oram.`bucket p;last by smt(mem_cat).
    move : (Hne (p ++ (nseq (_oram.`height - size p) false)) (size p) _);smt(List.size_ge0).
  move => *;split.
  + move => ?; split;1: smt().
  + move => *; split;1: smt(mem_cat).
  + move => *; split.
    + move => _c ?; case (_c = _b.`1); last first.
      + move => ne; move : (He _c _); 1: smt().
        move => Hec; elim Hec => i Hi; exists i => */=.
        rewrite hasP in Hi; rewrite hasP; smt(mem_cat).
      move => e; exists 0 => /=; rewrite hasP;smt(mem_cat take0).
  + move => *; split.
    + move => p1 p2 i1 i2.
      case (p1 = []); case (p2 = []);4:smt().
      +  move => -> -> /=; rewrite /"_.[_<-_]" /= !size_cat /= /"_.[_]" /= !nth_cat /=.
         case (i1 = size (_oram.`bucket []));case (i2 = size (_oram.`bucket []));
         1,4:smt().
         + move => ??????; rewrite ifF 1:/# ifT 1:/# ifT 1:/#.
           move : (Hne (nseq _oram.`height false) 0 _ _); smt(size_nseq mem_nth).
         + move => ??????; rewrite ifT 1:/# ifF 1:/# ifT 1:/#.
           move : (Hne (nseq _oram.`height false) 0 _ _); smt(size_nseq mem_nth).
      +  move => ? -> /=; rewrite /"_.[_<-_]" /= !size_cat /= /"_.[_]" /= !nth_cat /=.
         case (i1 = size (_oram.`bucket []));2:smt().
         + move => ?????; rewrite ifF 1:/# ifT 1:/# ifF 1:/#.
           move : (Hne (p2 ++ (nseq (_oram.`height - size p2) false)) (size p2) _ _);smt(List.size_ge0 size_cat size_nseq  mem_nth).
      +  move => -> ? /=; rewrite /"_.[_<-_]" /= !size_cat /= /"_.[_]" /= !nth_cat /=.
         case (i2 = size (_oram.`bucket []));2:smt().
         + move => ?????; rewrite ifF 1:/# ifF 1:/# ifT 1:/#.
           move : (Hne (p1 ++ (nseq (_oram.`height - size p1) false)) (size p1) _ _); smt(List.size_ge0 size_cat size_nseq  mem_nth).
  + move => ? p ? i ?? b;rewrite /"_.[_<-_]" /=.
    case (p = [] \/ i <= 0).
    + move => ?; rewrite ifT 1:/# /= mem_cat /= => H; elim H.
      + move => *; move : (Hf p _ 0 _ b _);smt(take0).
      + move => Hb; split;smt(List.size_ge0).
    + move => ?; rewrite ifF;  smt().
by smt().
qed.


lemma equiv_flush (_C : cell -> bool) (_oram : oram) (_soram : soram)  (_h : int) :
    equiv[ORAM.flush ~ SimpleORAM.flush :
         arg{1} = (_oram)
      /\ arg{2} = (_soram)
      /\ oram_rel _C _h _oram _soram
      /\ leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2}
    ==>
         res{1}.`positions = _oram.`positions
      /\ res{2} = _soram
      /\   oram_rel _C _h res{1} res{2}
      /\ leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2}
  ].
  proof.
  proc => /=;seq 1 1 : (#pre /\ ={p} /\ size p{1} = _h);1: by auto => />;smt(supp_dlist).
  sp; elim* => _sl2.
  exists* ORAM.leakage{1}; elim* => _l1.
  while {1} (0 <= i{1} <= _h + 1
    /\ ={p} /\ size p{1} = _h
    /\ _h = oram{1}.`height
    /\ (oram_rel _C _h _oram _soram)
    /\ oram{1}.`positions = _oram.`positions
    /\ oram{2} = _soram
    (* Whatever is not in pushed is in the oram relation *)
    /\ (oram_rel  (predI _C (fun cc => size pushed{1} <= find (fun (b : block) => b.`1 = cc) pushed{1})) _h oram{1} oram{2})
    (* Whatever is in current oram first levels is not in pushed and it was somewhere above *)
    (*             in the original _oram *)
    /\ (forall _p, size _p < i{1} =>
       (all (fun (block : block) =>
           !block \in pushed{1} /\
            (exists ii, 0<= ii <= size _p /\ block \in _oram.`bucket (take ii _p)))  (oram{1}.`bucket _p)))
    (* Whatever is in current oram later levels is untouched from _oram *)
    /\ (forall _p, i{1} <= size _p <= oram{1}.`height => oram{1}.`bucket _p = _oram.`bucket _p)
    (* block is in pushed iff it was higher up in the path of _oram and agrees on the path *)
    /\ (forall bb, bb \in pushed{1} <=> (i{1} <= _h /\
           take i{1} bb.`2 = take i{1} p{1} /\ exists ii,  0<=ii<i{1} /\ bb \in _oram.`bucket (take ii p{1})))
    (* we have no repeats in pushed *)
    /\ (forall i1 i2, 0 <= i1 < size pushed{1} => 0 <= i2 < size pushed{1} =>
                       pushed{1}.[i1].`1 = pushed{1}.[i2].`1 => i1 = i2)
    /\ (leakage_rel _h _l1 _sl2)
    /\ (leakage_rel (i{1}-1) (take (2*i{1}) ORAM.leakage{1}) [Flush p{2}])
    /\ drop (2*i{1}) ORAM.leakage{1} = _l1
    /\ SimpleORAM.leakage{2} = Flush p{2} :: _sl2
  ) (_h + 1 - i){1}.
  + auto => /> &hr [#] 11? Hbase Hinjb Hps 6? H 4? H0 ? H01 ?? H1 H2 H3 H4 leakage 2? /=.
    pose newpushed := (if i{hr} = oram{hr}.`height then []
        else
          filter
            (fun (block : block) =>
               take (i{hr} + 1) block.`2 = take (i{hr} + 1) p{m})
            (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m}))) .
    pose stayhere := if i{hr} = oram{hr}.`height then
                 pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})
               else
                 filter
                   (fun (block : block) =>
                      take (i{hr} + 1) block.`2 <> take (i{hr} + 1) p{m})
                   (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})).
    (* setting the ground *)
    have ? : forall b, (!b \in newpushed /\ !b \in stayhere) => !b \in pushed{hr}.
    + case (i{hr} = oram{hr}.`height); 1: by smt(mem_cat).
      by rewrite /newpushed /stayhere => ->b /=; rewrite !mem_filter !mem_cat /#.

    have ? : forall b, b \in stayhere => !b \in pushed{hr} => b \in oram{hr}.`bucket (take i{hr} p{m}).
    + rewrite /stayhere;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
       by move => b;rewrite !mem_filter !mem_cat /#.

    have ? : forall b, b \in newpushed => !b \in pushed{hr} => b \in oram{hr}.`bucket (take i{hr} p{m}).
    + rewrite /newpushed;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
       by move => b;rewrite !mem_filter !mem_cat /#.

    have ? : forall b, b \in stayhere => !b \in newpushed.
    + rewrite /stayhere /newpushed;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
       by move => b;rewrite !mem_filter !mem_cat /#.

    have ? : forall b, !b \in stayhere => !b \in newpushed =>
      !b \in oram{hr}.`bucket (take i{hr} p{m}).
    + rewrite /stayhere /newpushed;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
       by move => b;rewrite !mem_filter !mem_cat /#.

    have Hsep : forall bb pp, size pp <= oram{hr}.`height =>
         bb \in oram{hr}.`bucket.[take i{hr} p{m} <- stayhere] pp =>
          size newpushed <= find (fun (b : block) => b.`1 = bb.`1) newpushed.
    +  move => bb pp ??;
       have [ _ Hin]  := find_rng_in newpushed (fun (b : block) => b.`1 = bb.`1).
       rewrite implybE in Hin;elim Hin;1: by smt(find_ge0).
       rewrite hasP=> Hex;elim Hex => b2 /= *.
       case (b2 \in stayhere) => *; 1: by smt().
       case (i{hr} < size pp) => *.  (* block is below *)
        + have ? : bb \in _oram.`bucket pp by smt(size_take).
          pose i1 := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket pp).
          have i1b := find_rng_in (_oram.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
          case (b2 \in pushed{hr}) => Hb2.
            + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i2' p{m})).
              have := Hinjb (take i2' p{m}) pp i2f i1 _ _ _;2,4:smt(size_take nth_find mem_nth).
              + have := (find_rng_in (_oram.`bucket (take i2' p{m})) (fun (bf : block) => bf.`1 = b2.`1));1: by rewrite hasP; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i2' p{m})) _;1: by rewrite ?
hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _;rewrite ?
hasP /=; smt().
          have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
          pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})).
          have := Hinjb (take i{hr} p{m}) pp i2f i1 _ _ _;2,4:smt().
              + have :=  find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
              have /= :=  nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})) _;1: by rewrite hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _; by rewrite ?hasP /=; smt().
        case (size pp < i{hr}) => *.
        (* block is above *)
        + have ? : pp <> take i{hr} p{m} by smt(size_take).
          move : (H1 pp _); 1: by smt().
          rewrite allP => /> Hbs; move : (Hbs bb _);1:smt().
          move =>  [#? Hex];elim Hex => i1' *.
          have ? : bb \in _oram.`bucket (take i1' pp) by smt().
          pose i1f := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket (take i1' pp)).
          case (b2 \in pushed{hr}) => Hb2.
            + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i2' p{m})).
              have := Hinjb (take i2' p{m}) (take i1' pp) i2f i1f _ _ _; 4:  by smt().
              + have := find_rng_in (_oram.`bucket (take i2' p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
              + have := find_rng_in (_oram.`bucket (take i1' pp)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i2' p{m})) _;by rewrite ?hasP /=; smt().

          have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
          pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})).
          have := Hinjb (take i{hr} p{m}) (take i1' pp) i2f i1f _ _ _;4:smt(size_take).
          + have := find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
          + have := find_rng_in (_oram.`bucket (take i1' pp)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
          have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})) _;1: by rewrite ?hasP;smt(nth_find).
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket (take i1' pp)) _; by rewrite ?hasP /=; smt().

        + (* block is at this level *)
          case (pp = take i{hr} p{m}) => *; last first.
          + have Hinn : bb \in _oram.`bucket pp by smt().
          pose i1 := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket pp).
          have i1b := find_rng_in (_oram.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
          case (b2 \in pushed{hr}) => Hb2.
            + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i2' p{m})).
              have := Hinjb (take i2' p{m}) pp i2f i1 _ _ _;2,4:smt(size_take).
              + have := find_rng_in (_oram.`bucket (take i2' p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i2' p{m})) _;1: by rewrite ?hasP;smt(nth_find).
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _; by rewrite ?hasP /=; smt().

            have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
            pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})).
            have := Hinjb (take i{hr} p{m}) pp i2f i1 _ _ _;2,4:smt(size_take).
            + have := find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
            have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})) _;1: by rewrite ?hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _; by rewrite ?hasP /=; smt().

        + have ? : bb \in stayhere;1: by smt().
          case (bb \in pushed{hr}) => Hpps;last first.
          +  have ? : bb \in (_oram.`bucket pp) by smt().
             pose i1 := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket pp).
             have i1b := find_rng_in (_oram.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
             case (b2 \in pushed{hr}) => Hb2.
              + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
                pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i2' p{m})).
                have := Hinjb (take i2' p{m}) pp i2f i1 _ _ _;2,4:smt().
                + have := find_rng_in (_oram.`bucket (take i2' p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
                have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i2' p{m})) _;1: by rewrite ?hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _; by rewrite ?hasP /=; smt().

             have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt().
             pose i2f := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket (take i{hr} p{m})).
             have := Hinjb (take i{hr} p{m}) pp i2f i1 _ _ _;2,4:smt().
             + have := find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
             have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})) _; by rewrite ?hasP /=; smt().

             case (b2 \in pushed{hr}) => Hb2.
              + pose i1f := find (pred1 bb) pushed{hr}.
                pose i2f := find (pred1 b2) pushed{hr}.
                move : (H4 i1f i2f); smt().

             move : (H3 bb);rewrite Hpps /= => [#?? Hex];elim Hex => i1' *.
             pose i1f := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket (take i1' p{m})).
             have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt().
             pose i2f := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket (take i{hr} p{m})).
             have := Hinjb (take i{hr} p{m}) (take i1' p{m}) i2f i1f _ _ _;3..:smt().
             + have := find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
             + have := find_rng_in (_oram.`bucket (take i1' p{m})) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().

       have Hinjf : forall bb1 bb2 pp1 pp2, bb1 \in _oram.`bucket pp1 => bb2 \in _oram.`bucket pp2 =>
                 bb1.`1 = bb2.`1 => pp1 <> pp2 => false.
         move => bb1 bb2 pp1 pp2 Hl1 Hl2 Hl3 Hl4.
         pose i1f := find (fun (bf : block) => bf.`1 = bb1.`1) (_oram.`bucket pp1).
         pose i2f := find (fun (bf : block) => bf.`1 = bb2.`1) (_oram.`bucket pp2).
         have := Hinjb pp1 pp2 i1f i2f _ _ _.
              + have := find_rng_in (_oram.`bucket pp1) (fun (bf : block) => bf.`1 = bb1.`1); rewrite hasP; smt().
              + have := find_rng_in (_oram.`bucket pp2) (fun (bf : block) => bf.`1 = bb2.`1); rewrite hasP; smt().
                have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb1.`1)(_oram.`bucket pp1)_;1: by rewrite ?hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb2.`1) (_oram.`bucket pp2)  _; by rewrite ?hasP /=; smt().
               by smt(size_take).


    (* main proof *)
    do split;1,2,5,9..:smt(size_take).
    + move=>*; split;1: smt().
      move=>*; split.
      + move => pp ? bb Hb Hc Hnf.
        case (i{hr} < size pp); 1: by smt(size_take). (* block is below *)
        case (size pp < i{hr}) => *;1: by smt(allP). (* block is above *)
        by smt(). (* block is at this level *)
      move=>*; split;1: smt(size_take).
      move=>*; split.
      + move => pp ? bb Hbb; split;1: by
          case (i{hr} < size pp) => *;
          case (size pp < i{hr}) => *;smt().
     (* it remains to show not in newpushed *)
      by apply (Hsep bb pp).

      move=>*; split.
      + move => c Hc Hnh.
        case (size stayhere <= find (fun (b : block) => b.`1 = c) stayhere) => Hcs; last first.
        + (* storing it now: it's in stayhere *)
          exists i{hr}; split => *;1:smt().
          have  := find_rng_in stayhere (fun (b : block) => b.`1 = c).
          have -> /= : 0 <= find (fun (b : block) => b.`1 = c) stayhere < size stayhere
               by smt(List.size_ge0 find_ge0).
          rewrite hasP => Hex; elim Hex => bb *.
          rewrite hasP; exists bb.
          case (bb \in pushed{hr}) => Hip;last by move : (Hps p{m} _ i{hr} _);smt().
          by smt(block_props).
         + (* already in tree *)
           move : (H0 c _).
           + rewrite /predI /=;split;1:smt().
              have  := find_rng_out stayhere (fun (b : block) => b.`1 = c).
              have  := find_rng_out newpushed (fun (b : block) => b.`1 = c).
              have  := find_rng_out pushed{hr} (fun (b : block) => b.`1 = c).
              rewrite !hasP !negb_exists /=; smt().
           move => H0c; elim H0c => i' [#?? Hb]; exists i';do split;1,2:smt().
           rewrite hasP in Hb; elim Hb => bb /= *.
           rewrite hasP; exists bb => /=.
           case (i' < i{hr}) => *; 1: by smt(size_take). (* block is below *)
           case (i{hr} = i') => *; last by smt(size_take).
           + have ? : take i{hr} p{m} <> (take i' (oram{hr}.`positions c)); last by smt().
             have  := find_rng_out stayhere (fun (b : block) => b.`1 = c).
             have  := find_rng_out newpushed (fun (b : block) => b.`1 = c).
             have  := find_rng_out (oram{hr}.`bucket (take (i{hr}) p{m})) (fun (b : block) => b.`1 = c).
             rewrite !hasP !negb_exists /=.
             have -> /= : ! find (fun (b : block) => b.`1 = c) newpushed < size newpushed by smt().
             have -> /= : ! find (fun (b : block) => b.`1 = c) stayhere < size stayhere by smt().
             move => Hib Hinp Hish; move : (Hinp bb); move : (Hish bb); rewrite  (: bb.`1 = c) 1:/# /=.
             by smt().

      move=>*; split.
      + move => p1 p2 i1 i2 ????.
        (* begin injectivity *)
        rewrite /"_.[_<-_]".
        case (take i{hr} p{m} = p1);
        case (take i{hr} p{m} = p2) => ??; last by smt().
        + rewrite /stayhere; case (i{hr} = oram{hr}.`height) => ?.
          + rewrite /"_.[_]" !nth_cat.
            case (i1 < size pushed{hr}); case (i2 < size pushed{hr}) => ??;1,4 : smt(size_cat size_filter List.size_ge0).
            + move => ?; pose b1 := nth witness pushed{hr} i1.
              pose b2 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (i2 - size pushed{hr}).
              have Hb1 : b1 \in pushed{hr} by smt(mem_nth).
              have Hb2 : b2 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
              by smt(size_take).
            + move => ?; pose b2 := nth witness pushed{hr} i2.
              pose b1 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (i1 - size pushed{hr}).
              have Hb2 : b2 \in pushed{hr} by smt(mem_nth).
              have Hb1 : b1 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
              smt(size_take).

          + have /= HH := (filter_inj
                  (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m}))
                  (fun (b : block) => b.`1)
                  (fun (block : block) => take (i{hr} + 1) block.`2 <> take (i{hr} + 1) p{m})).
            have ? : (forall (i1 i2 : int),
              0 <= i1 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) =>
              0 <= i2 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) =>
                 (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) i1).`1 =
                 (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) i2).`1 =>
                    i1 = i2) ; last by smt().
            move => ii1 ii2 ??.
          + rewrite /"_.[_]" !nth_cat.
            case (ii1 < size pushed{hr}); case (ii2 < size pushed{hr}) => ??;1,4:smt(size_cat size_filter List.size_ge0).
            + move => ?; pose b1 := nth witness pushed{hr} ii1.
              pose b2 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (ii2 - size pushed{hr}).
              have Hb1 : b1 \in pushed{hr} by smt(mem_nth).
              have Hb2 : b2 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(mem_nth size_cat size_filter List.size_ge0).
              by smt(size_take).

            + move => ?; pose b2 := nth witness pushed{hr} ii2.
              pose b1 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (ii1 - size pushed{hr}).
              have Hb2 : b2 \in pushed{hr} by smt(mem_nth).
              have Hb1 : b1 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
              by smt(size_take).

        + pose b1 := stayhere.[i1].
          pose b2 := (oram{hr}.`bucket p2).[i2].
          move => ?.
          have Hb2 : b2 \in oram{hr}.`bucket p2 by smt(mem_nth).
          have  : b1 \in stayhere by smt(mem_nth).
          rewrite /stayhere => ?.
          case (b1 \in pushed{hr}) => Hb1.
          + have := H3 b1; rewrite Hb1 /= => [#?? Hex];elim Hex => i1' *.
            case (i{hr} < size p2) => *.
            + have ? : b2 \in _oram.`bucket p2 by smt(mem_nth).
              by smt(size_take).

            case (i{hr} = size p2) => *.
            + have ? : b2 \in _oram.`bucket p2 by smt(mem_nth).
              by smt(size_take).

            + have := H1 p2 _;1:smt().
              rewrite allP => H1p2; move : (H1p2 b2 _) => /=;1:smt().
              move => [#? Hex];elim Hex => i2' *.
              by smt(size_take).

          + have Hbb1 : b1 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
            case (i{hr} < size p2) => *.
            + have Hbb2 : b2 \in _oram.`bucket p2 by smt(mem_nth).
              by smt(size_take).
            case (i{hr} = size p2) => *.
            + have Hbb2 : b2 \in _oram.`bucket p2 by smt(mem_nth).
              by smt(size_take).
            + have := H1 p2 _;1:smt().
              rewrite allP => H1p2; move : (H1p2 b2 _) => /=;1:smt().
              move => [#? Hex];elim Hex => i2' *.
              by smt(size_take).

        + pose b2 := stayhere.[i2].
          pose b1 := (oram{hr}.`bucket p1).[i1].
          move => ?.
          have Hb1 : b1 \in oram{hr}.`bucket p1 by smt(mem_nth).
          have  : b2 \in stayhere by smt(mem_nth).
          rewrite /stayhere => ?.
          case (b2 \in pushed{hr}) => Hb2.
          + have := H3 b2; rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
            case (i{hr} < size p1) => *.
            + have ? : b1 \in _oram.`bucket p1 by smt(mem_nth).
              by smt(size_take).
            case (i{hr} = size p1) => *.
            + have ? : b1 \in _oram.`bucket p1 by smt(mem_nth).
              by smt(size_take).
            + have := H1 p1 _;1:smt().
              rewrite allP => H1p1; move : (H1p1 b1 _) => /=;1:smt().
              move => [#? Hex];elim Hex => i1' *.
              by smt(size_take).
          + have Hbb2 : b2 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
            case (i{hr} < size p1) => *.
            + have Hbb1 : b1 \in _oram.`bucket p1 by smt(mem_nth).
              by smt(size_take).
            case (i{hr} = size p1) => *.
            + have Hbb1 : b1 \in _oram.`bucket p1 by smt(size_take).
              by smt(size_take).
            + have := H1 p1 _;1:smt().
              rewrite allP => H1p1; move : (H1p1 b1 _) => /=;1:smt().
              move => [#? Hex];elim Hex => i1' *.
              by smt(size_take).
      (* end injectivity*)

      + move => ? pp Hpp ii ?? bb Hbb.
        case (size (take ii pp) <= i{hr}) => *; last first.
        + (* bb is below *)
          have ?: bb \in oram{hr}.`bucket (take ii pp) by smt(size_take).
          move : (H2 (take ii pp) _); 1:smt().
          move : (Hps pp _ ii _); smt(size_take).
        case (size (take ii pp) < i{hr}) => *.
        + (* bb is above *)
          have ?: bb \in oram{hr}.`bucket (take ii pp) by smt(size_take).
          move : (H01 pp _ ii _ bb _); smt(size_take).
        (* bb is at level i{hr} *)
        case (take i{hr} p{m} = take i{hr} pp) => *; last first.
        + (* other path *)
          have ?: bb \in _oram.`bucket (take ii pp);  by smt(take_oversize size_take).
          move : (Hps pp _ ii _);smt(size_take).
        (* this path *)

      + move => pp ?; rewrite allP => bb Hbb /=; split;last first.
        (* basic properties *)
        case (size pp < i{hr}) => Hsp.
        + move : Hbb (H1 pp Hsp); rewrite !allP /"_.[_<-_]" /=.
          rewrite ifF; smt(size_take).
        case (i{hr} < size pp) => Hspp.
        + move : Hbb (H2 pp); rewrite /"_.[_<-_]" /=.
          rewrite ifF; smt(size_take).
        (* bb is at level i{hr} *)
        case (take i{hr} p{m} = take i{hr} pp) => *; last first.
        + (* other path *)
          have ?: bb \in _oram.`bucket (take i{hr} pp) by smt(take_oversize size_take).
          move : (Hps pp _ i{hr} _);smt().
        (* this path *)
        have ? : bb \in stayhere by smt(take_oversize size_take).
        case (bb \in pushed{hr}) => Hip.
        + move => *. move : (H3 bb); rewrite Hip /= => [#] ??Hex.
          elim Hex => ii *; exists ii.
          +  have ? : (take ii p{m}) = (take ii pp); last by smt().
             apply (eq_from_nth witness);smt(size_take nth_take).
         have ? : bb \in _oram.`bucket (take i{hr} pp) by smt(take_size).
            have := block_props _C _oram bb (take i{hr} pp) _; last by smt().
            + rewrite /is_oram.
              move => *; do split; 1:smt().
              move => *; do split; 1:smt().
              move => *; do split; 1:smt().
              move => *; do split; 1:smt().
              move => *; do split =>/=; 1: by apply Hbase.
              move => *; do split; 1:smt().
              move => *; do split; 1:smt().
              smt().
       (* it remains to prove not in newpushed *)
       have := Hsep bb pp _ _;1,2: smt().
       have := find_rng_out newpushed (fun (b : block) => b.`1 = bb.`1) .
       rewrite hasP => /=;smt().

      + move => bb; case (i{hr} = oram{hr}.`height) =>*;1: by smt().
          + rewrite /newpushed ifF 1:/# /=;split.
          + move => H';do split;1:smt().
            + rewrite mem_filter /= in H';smt().
            case (bb \in pushed{hr}); by smt(size_take).
          + move => ? Ht ii *;rewrite mem_filter mem_cat /=;split;1:smt().
            case (bb \in pushed{hr}); 1: smt().
            rewrite H3 /=.
            have -> /= : i{hr} <= size p{m} by smt().
            have -> /= : take i{hr} bb.`2 = take i{hr} p{m}; last by smt(size_take).
            + move : Ht;rewrite !(take_nth witness); first last;1,3:smt().
            rewrite -!cats1 eqseq_cat; last by smt().
            smt(size_take).

    + rewrite /newpushed /"_.[_]" /=.
      case (i{hr} = oram{hr}.`height) => ?; 1:smt().
      have /= HH := (filter_inj
         (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m}))
         (fun (b : block) => b.`1)
         (fun (block : block) => take (i{hr} + 1) block.`2 = take (i{hr} + 1) p{m})).
      have ? : (forall (i1 i2 : int),
       0 <= i1 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) =>
       0 <= i2 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) =>
       (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) i1).`1 =
       (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) i2).`1 =>
       i1 = i2) ; last by smt().
       move => i1 i2 ??.
          + rewrite /"_.[_]" !nth_cat.
            case (i1 < size pushed{hr}); case (i2 < size pushed{hr}) => ??;1,4:smt(size_cat size_filter List.size_ge0).
            + move => ?; pose b1 := nth witness pushed{hr} i1.
              pose b2 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (i2 - size pushed{hr}).
              have Hb1 : b1 \in pushed{hr} by smt(mem_nth).
              have Hb2 : b2 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
              move : (H3 b1);rewrite Hb1 /= => [#?? Hex];elim Hex => i1' *.
              smt(size_take).

            + move => ?; pose b2 := nth witness pushed{hr} i2.
              pose b1 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (i1 - size pushed{hr}).
              have Hb2 : b2 \in pushed{hr} by smt(mem_nth).
              have Hb1 : b1 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
              move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              smt(size_take).

    + rewrite !ifF 1,2:/# /leakages_of_sleakages /=.
      simplify leakages_of_sleakage => /=.
      rewrite flatten1 /= rangeSr 1:/# /= rev_rcons /= flatten_cons.
      rewrite !cat_cons cat0s;do congr.
      have -> : (2 * (i{hr} + 1) - 2)  = 2*i{hr}  by ring.
      rewrite -leakage /leakages_of_sleakages /=.
      simplify leakages_of_sleakage => /=.
      by rewrite flatten1 /#.

  auto => /> &1 &2 *; do split;1,2,7:smt().
  +  by smt(size_take).
  +  by smt(size_take).
  +  by smt(size_take).
  + rewrite /leakages_of_sleakages take0 /=.
    simplify leakages_of_sleakage => /=.
      by rewrite range_geq //=.
  move => leakl il oraml pushedl; do split;1:by smt(size_take).
  move => 8? Hor 4? Hhas 8? l1 l2; do split.
  + move => *; do split;1:smt(size_take).
    move => *; do split.
    + move => p Hp b Hb Hc.
      have : forall b, !b \in  pushedl by smt().
      move : (Hor p _ b _ _);1,2,4:  smt(size_take).
      rewrite /predI /=;split; 1:smt().
      move => *.
      rewrite lezNgt -has_find hasP /#.
    move => *; do split.
    + smt(size_take).
    move => ?c Hc.
    move : (Hhas c _); last by smt(size_take).
      + rewrite /predI /=; split; 1:smt().
      have := find_rng_out pushedl (fun (bb : block) => c = bb.`1).
      rewrite hasPn; by smt(size_take).

  have := cat_take_drop (2*il) leakl;rewrite -l1 l2 /leakages_of_sleakages /= => <-.
  rewrite flatten_cons;congr.
  simplify leakages_of_sleakage => /=.
  by rewrite flatten1 /#.
qed.

lemma equiv_compile (_oram : oram) (_soram : soram)  (_h : int) (_p : prog) :
equiv[ORAM.compile ~ SimpleORAM.compile :
         arg{1} = (_oram,_p)
      /\ arg{2} = (_soram,_p)
      /\ (forall cc, _oram.`positions cc = (_soram.`smap cc).`1)
      /\ (forall ii cc, (0 <= ii < size _p /\
              isRd _p.[ii] /\ varV _p.[ii] = cc) =>
           (exists jj, 0 <= jj < ii /\ isWt _p.[jj] /\ varV _p.[jj] = cc))
      /\ oram_rel pred0 _h _oram _soram
      /\ leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2}
    ==>
         oram_rel (fun c => exists i, 0<=i<size _p /\
               isWt _p.[i]  /\ varV _p.[i] = c)  _h res{1}.`1 res{2}.`1
      /\ res{1}.`2 = res{2}.`2
      /\ res{1}.`1 = res{1}.`1
      /\ leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2}
  ].
proof.
proc => /=.
while (#{/~o{1}}{~o{2}}pre
     /\ ={i,os}
     /\ 0 <= i{1} <= size _p
      /\ (forall cc, _oram.`positions cc = (_soram.`smap cc).`1)
     /\ (forall cc, (!(exists ii, 0<=ii<i{1} /\
               isWt _p.[ii] /\ varV _p.[ii] = cc)) =>
           o{1}.`positions cc = (o{2}.`smap cc).`1)
     /\ oram_rel (fun c => exists ii, 0<=ii<i{1} /\
               isWt _p.[ii] /\ varV _p.[ii] = c) _h o{1} o{2});
   last by auto => /> *;do split; smt(List.size_ge0).

match;1,2:smt().
+ move => _c1 _c2.
  inline{1} 1; inline {2} 1;sp => /=.

  seq 1 1 : (={os} /\
  c{2} = _c2 /\
  c{1} = _c1 /\
  nth witness p{1} i{1} = Rd _c1 /\
  nth witness p{2} i{2} = Rd _c2 /\
  p{1} = _p /\
  p{2} = _p /\
  (forall (ii : int) (cc : cell),
       (0 <= ii < size _p /\ isRd _p.[ii] /\ varV _p.[ii] = cc) =>
       exists (jj : int), 0 <= jj < ii /\ isWt _p.[jj] /\ varV _p.[jj] = cc) /\
  oram_rel pred0 _h _oram _soram /\
  leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2} /\
   ={i} /\
  0 <= i{1} <= size _p /\
  (forall cc, _oram.`positions cc = (_soram.`smap cc).`1) /\
  (forall cc, (!(exists ii, 0<=ii<i{1} /\
               isWt _p.[ii] /\ varV _p.[ii] = cc)) =>
           oram{1}.`positions cc = (oram{2}.`smap cc).`1) /\
  oram_rel
     (predI
        (fun c0 => exists (ii : int),
          0 <= ii < i{1} /\ isWt _p.[ii] /\ varV _p.[ii] = c0) (predC1 _c1)) _h oram{1} oram{2} /\
  (forall p i, 0 <= i <= oram{1}.`height =>
                           size p = oram{1}.`height =>
                let block = oram{1}.`bucket (take i p) in
                 !(has (fun (block : block) => block.`1 = _c1) block)) /\
  ={block} /\ block{2}.`1 = _c1 /\
  i{1} < size p{1} /\ i{2} < size p{2}
  );1: by ecall(equiv_fetch (fun c => exists ii, 0 <= ii < i{1} /\
               isWt _p.[ii] /\ varV _p.[ii] = c) oram{1} oram{2} c{1} _h);auto => /> /#.

  seq 1 1 : (#pre /\ ={pos} /\ size pos{1} = _h); 1: by auto => />;smt(supp_dlist).

  seq 1 0 : (={os} /\
   c{2} = _c2 /\
  c{1} = _c1 /\
  nth witness p{1} i{1} = Rd _c1 /\
  nth witness p{2} i{2} = Rd _c2 /\
  p{1} = _p /\
  p{2} = _p /\
  (forall (ii : int) (cc : cell),
       (0 <= ii < size _p /\ isRd _p.[ii] /\ varV _p.[ii] = cc) =>
       exists (jj : int), 0 <= jj < ii /\ isWt _p.[jj] /\ varV _p.[jj] = cc) /\
  oram_rel pred0 _h _oram _soram /\
  leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2} /\
   ={i} /\
  0 <= i{1} <= size _p /\
  (forall cc, _oram.`positions cc = (_soram.`smap cc).`1) /\
  (forall cc, (!(exists ii, 0<=ii<i{1}+1 /\
               isWt _p.[ii] /\ varV _p.[ii] = cc)) =>
           oram{1}.`positions cc = (oram{2}.`smap cc).`1) /\
  oram_rel
     (predI
        (fun c0 => exists (ii : int),
          0 <= ii < i{1} /\ isWt _p.[ii] /\ varV _p.[ii] = c0) (predC1 _c1)) _h oram{1} oram{2} /\
  (forall p i, 0 <= i <= oram{1}.`height =>
                           size p = oram{1}.`height =>
                let block = oram{1}.`bucket (take i p) in
                 !(has (fun (block : block) => block.`1 = _c1) block)) /\
  ={block} /\ block{2}.`1 = _c1 /\ ={pos} /\ size pos{1} = _h /\
  i{1} < size p{1} /\ i{2} < size p{2} /\
   oram{1}.`positions _c1 = pos{1}
  ).
  + auto => /> &1 &2 21? Hpos 5? He ? Hp ?? Hne 2?; do split.
    + smt().
    + move => *; do split.
      + move => _i *.
        case ( (exists (ii : int),
          0 <= ii < i{2} /\ isWt _p.[ii] /\ varV _p.[ii] = (varV _p.[_i]))) => *;2: smt(size_take).
        move : (Hpos (varV _p.[_i]) _); smt().
      move => *; do split; 1:smt(size_take).
      move => *; do split.
      + move => ii *; move : (He  (varV _p.[ii]) _); 1: smt().
        move => Hen; elim Hen => jj *.
        exists jj. smt(size_take).
      move => ??pp? ii??bb?; split; last by smt().
      case (block{2}.`1 = bb.`1); last by move : (Hp pp _ ii _ bb _);smt().
      move => ?; move : (Hne (pp++nseq (oram{1}.`height - size pp) false) ii _ _);1,2:smt(size_take).
      move => ?; move : (Hne (pp++nseq (oram{1}.`height - size pp) false) (size pp) _ _);1,2:smt(size_take).
      by smt(size_take).

  seq 1 1 : (={os} /\
   c{2} = _c2 /\
  c{1} = _c1 /\
  nth witness p{1} i{1} = Rd _c1 /\
  nth witness p{2} i{2} = Rd _c2 /\
  p{1} = _p /\
  p{2} = _p /\
  (forall (ii : int) (cc : cell),
       (0 <= ii < size _p /\ isRd _p.[ii] /\ varV _p.[ii] = cc) =>
       exists (jj : int), 0 <= jj < ii /\ isWt _p.[jj] /\ varV _p.[jj] = cc) /\
  oram_rel pred0 _h _oram _soram /\
  leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2} /\
   ={i} /\
  0 <= i{1} <= size _p /\
  (forall cc, _oram.`positions cc = (_soram.`smap cc).`1) /\
  (forall cc, (!(exists ii, 0<=ii<i{1}+1 /\
               isWt _p.[ii] /\ varV _p.[ii] = cc)) =>
           oram{1}.`positions cc = (oram{2}.`smap cc).`1) /\
  oram_rel
     (fun c0 => exists (ii : int),
          0 <= ii < i{1} + 1 /\ isWt _p.[ii] /\ varV _p.[ii] = c0) _h oram{1} oram{2} /\
  ={block} /\ block{2}.`1 = _c1 /\ ={pos} /\ size pos{1} = _h /\
  i{1} < size p{1} /\ i{2} < size p{2}).
  wp;ecall(equiv_putback (predI (fun cc => exists ii, 0 <= ii < i{1} + 1 /\
               isWt _p.[ii] /\ varV _p.[ii] = cc) (predC1 _c1)) oram{1} oram{2}
     (block{1}.`1, oram{1}.`positions block{1}.`1, block{1}.`3)  _h).
  + auto => /> &1 &2 35?; do split.
    + move => /> *; do! split; smt().
    + move => 14? rr1 rr2 5? Hpm Hpr 4? Hw ? Hp 2?; do split;1:smt().
      + move => *; do split.
        move => _i *.
        case ( (exists (ii : int),
          0 <= ii < i{2} /\ isWt _p.[ii] /\ varV _p.[ii] = (varV _p.[_i]))) => *;2: smt(size_take).
        move : (Hpm (varV _p.[_i]) _); smt().
        move => *; do split.
        move => pp? bb?ii????.
        move : (Hpr pp _ bb _);smt().
      + move => *; do split. smt().
      move => ? ii *;  move : (Hw (varV _p.[ii]) _); smt().

  wp;ecall(equiv_flush (fun c => exists ii, 0 <= ii < i{1} + 1 /\
               isWt _p.[ii] /\ varV _p.[ii] = c) oram{1} oram{2} _h).
  by auto => /> /#.

move => _cv1 _cv2.
  inline{1} 1; inline {2} 1;sp => /=.

  seq 1 1 : (={os} /\
  c{2} = _cv2.`1 /\
  c{1} = _cv1.`1 /\
  v0{2} = _cv2.`2 /\
  v0{1} = _cv1.`2 /\
  nth witness p{1} i{1} = Wt _cv1 /\
  nth witness p{2} i{2} = Wt _cv2 /\
  p{1} = _p /\
  p{2} = _p /\
  (forall (ii : int) (cc : cell),
       (0 <= ii < size _p /\ isRd _p.[ii] /\ varV _p.[ii] = cc) =>
       exists (jj : int), 0 <= jj < ii /\ isWt _p.[jj] /\ varV _p.[jj] = cc) /\
  oram_rel pred0 _h _oram _soram /\
  leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2} /\
   ={i} /\
  0 <= i{1} <= size _p /\
  (forall cc, _oram.`positions cc = (_soram.`smap cc).`1) /\
  (forall cc, (!(exists ii, 0<=ii<i{1} /\
               isWt _p.[ii] /\ varV _p.[ii] = cc)) =>
           oram{1}.`positions cc = (oram{2}.`smap cc).`1) /\
  oram_rel
     (predI
        (fun c0 => exists (ii : int),
          0 <= ii < i{1} /\ isWt _p.[ii] /\ varV _p.[ii] = c0) (predC1 _cv1.`1)) _h oram{1} oram{2} /\
  (forall p i, 0 <= i <= oram{1}.`height =>
                           size p = oram{1}.`height =>
                let block = oram{1}.`bucket (take i p) in
                 !(has (fun (block : block) => block.`1 = _cv1.`1) block)) /\
  i{1} < size p{1} /\ i{2} < size p{2}
  );1: by ecall(equiv_fetch (fun c => exists ii, 0 <= ii < i{1} /\
               isWt _p.[ii] /\ varV _p.[ii] = c) oram{1} oram{2} c{1} _h);auto => /> /#.

  seq 1 1 : (#pre /\ ={pos} /\ size pos{1} = _h); 1: by auto => />;smt(supp_dlist).

  seq 1 0 : (={os} /\
  c{2} = _cv2.`1 /\
  c{1} = _cv1.`1 /\
  v0{2} = _cv2.`2 /\
  v0{1} = _cv1.`2 /\
  nth witness p{1} i{1} = Wt _cv1 /\
  nth witness p{2} i{2} = Wt _cv2 /\
  p{1} = _p /\
  p{2} = _p /\
  (forall (ii : int) (cc : cell),
       (0 <= ii < size _p /\ isRd _p.[ii] /\ varV _p.[ii] = cc) =>
       exists (jj : int), 0 <= jj < ii /\ isWt _p.[jj] /\ varV _p.[jj] = cc) /\
  oram_rel pred0 _h _oram _soram /\
  leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2} /\
   ={i} /\
  0 <= i{1} <= size _p /\
  (forall cc, _oram.`positions cc = (_soram.`smap cc).`1) /\
  (forall cc, (!(exists ii, 0<=ii<i{1}+1 /\
               isWt _p.[ii] /\ varV _p.[ii] = cc)) =>
           oram{1}.`positions cc = (oram{2}.`smap cc).`1) /\
  oram_rel
     (predI
        (fun c0 => exists (ii : int),
          0 <= ii < i{1} /\ isWt _p.[ii] /\ varV _p.[ii] = c0) (predC1 _cv1.`1)) _h oram{1} oram{2} /\
  (forall p i, 0 <= i <= oram{1}.`height =>
                           size p = oram{1}.`height =>
                let block = oram{1}.`bucket (take i p) in
                 !(has (fun (block : block) => block.`1 = _cv1.`1) block)) /\
  ={pos} /\ size pos{1} = _h /\
  i{1} < size p{1} /\ i{2} < size p{2} /\
   oram{1}.`positions _cv1.`1 = pos{1}
  ).
  + auto => /> &1 &2 21? Hpos 5? He ? Hp ?? Hne 2?; do split.
    + smt().
    + move => *; do split.
      + move => _i *.
        case ( (exists (ii : int),
          0 <= ii < i{2} /\ isWt _p.[ii]
             /\ varV _p.[ii] = (varV _p.[_i]))) => *;2: smt(size_take).
        move : (Hpos (varV _p.[_i]) _); smt().
      move => *; do split; 1:smt(size_take).
      move => *; do split.
      + move => ii *; move : (He  (varV _p.[ii]) _); 1: smt().
        move => Hen; elim Hen => jj *.
        exists jj. smt(size_take).
      move => ??pp? ii??bb?; split; last by smt().
      case (_cv1.`1 = bb.`1); last by move : (Hp pp _ ii _ bb _);smt().
      move => ?; move : (Hne (pp++nseq (oram{1}.`height - size pp) false) ii _ _);1,2:smt(size_take).
      move => ?; move : (Hne (pp++nseq (oram{1}.`height - size pp) false) (size pp) _ _);1,2:smt(size_take).
      by smt(size_take).

  seq 1 1 : (={os} /\
  c{2} = _cv2.`1 /\
  c{1} = _cv1.`1 /\
  v0{2} = _cv2.`2 /\
  v0{1} = _cv1.`2 /\
  nth witness p{1} i{1} = Wt _cv1 /\
  nth witness p{2} i{2} = Wt _cv2 /\
  p{1} = _p /\
  p{2} = _p /\
  (forall (ii : int) (cc : cell),
       (0 <= ii < size _p /\ isRd _p.[ii] /\ varV _p.[ii] = cc) =>
       exists (jj : int), 0 <= jj < ii /\ isWt _p.[jj] /\ varV _p.[jj] = cc) /\
  oram_rel pred0 _h _oram _soram /\
  leakage_rel _h ORAM.leakage{1} SimpleORAM.leakage{2} /\
   ={i} /\
  0 <= i{1} <= size _p /\
  (forall cc, _oram.`positions cc = (_soram.`smap cc).`1) /\
  (forall cc, (!(exists ii, 0<=ii<i{1}+1 /\
               isWt _p.[ii] /\ varV _p.[ii] = cc)) =>
           oram{1}.`positions cc = (oram{2}.`smap cc).`1) /\
  oram_rel
     (fun c0 => exists (ii : int),
          0 <= ii < i{1} + 1 /\ isWt _p.[ii] /\ varV _p.[ii] = c0) _h oram{1} oram{2} /\
  ={pos} /\ size pos{1} = _h /\
  i{1} < size p{1} /\ i{2} < size p{2}).
  wp;ecall(equiv_putback (predI (fun cc => exists ii, 0 <= ii < i{1} + 1 /\
               isWt _p.[ii] /\ varV _p.[ii] = cc) (predC1 _cv1.`1)) oram{1} oram{2}
     (c{1}, pos{1},v0{1})  _h).
  by auto => |> *; do split;smt().  (* Fixme: why does crush break this? *)
  wp;ecall(equiv_flush (fun c => exists ii, 0 <= ii < i{1} + 1 /\
               isWt _p.[ii] /\ varV _p.[ii] = c) oram{1} oram{2} _h).
  by auto => /> /#.
qed.

  (* -------------------------------------------------------------------- *)
  type ioram = {
    iheight  : int;
    counters : bool -> int;
    bpath    : path;
    ioverflow : bool -> bool;
  }.

  op is_ioram (oram : ioram) =
       0 < oram.`iheight
    && (forall b, 0 <= oram.`counters b)
    && size oram.`bpath < oram.`iheight.

  module InternalORAM = {
    proc fetch(oram : ioram) : ioram = {
      return oram;
    }

    proc flush(oram : ioram) : ioram = {
      var p : path;
      var b : bool;

      p <$ dlist {0,1} oram.`iheight;
      b <- p.[size oram.`bpath];
      
      if (isprefix oram.`bpath p) {
        oram <- {| oram with
          counters = oram.`counters.[b <- 0]; 
        |};
      }

      return oram;
    }

    proc putback(oram : ioram, p : path) : ioram = {
      var b : bool <- p.[size oram.`bpath];

      if (isprefix oram.`bpath p) {
        oram <- {| oram with
          counters = oram.`counters.[b <- oram.`counters b + 1];
          ioverflow = oram.`ioverflow.[b <- K %/ 2 <= oram.`counters b];
        |};
      }

      return oram;
    }

    proc oreadwrite(oram : ioram) : ioram  = {
      var p : path;
      oram <@ fetch(oram);
      p <$ dlist {0,1} oram.`iheight;
      oram <@ putback(oram, p);
      oram <@ flush(oram);
      return oram;
    }

    proc compile(o : ioram, p : prog) : ioram = {
      var i : int;
      i <- 0;
      while (i < size p) {
        o <@ oreadwrite(o);
        i <- i + 1;
      }
      return o;
    }
  }.

  op internal_rel (C : cell -> bool) (h : int) (oram : oram) (ioram : ioram) =
       oram.`height = h
    /\ ioram.`iheight = h
    /\ is_oram C oram
    /\ is_ioram ioram
    /\ (forall b,
          let pb = ioram.`bpath ++ [b] in
          let bcks : block list list =
            map (fun p => oram.`bucket p) (prefixes ioram.`bpath) in
            count
              (fun (b : block) => (isprefix pb b.`2))
              (flatten bcks)
            <= ioram.`counters b).

  op internal_rel_fetch (C: cell -> bool) (h : int) (c : cell) (oram : oram) (ioram : ioram) =
        oram.`height = h
     /\ ioram.`iheight = h
     /\ is_oram_fetch C c oram
     /\ is_ioram ioram
     /\ (forall b,
           let pb = ioram.`bpath ++ [b] in
           let bcks : block list list =
             map (fun p => oram.`bucket p) (prefixes ioram.`bpath) in
             count
               (fun (b : block) => (isprefix pb b.`2))
               (flatten bcks)
             <= ioram.`counters b).

   lemma internal_rel_is_oram (C : cell -> bool) (h : int) (oram : oram) (ioram : ioram) :
     internal_rel C h oram ioram => is_oram C oram.
   proof. by move=> @/internal_rel. qed.

   lemma internal_rel_is_ioram (C : cell -> bool) (h : int) (oram : oram) (ioram : ioram) :
     internal_rel C h oram ioram => is_ioram ioram.
   proof. by move=> @/internal_rel. qed.

   lemma internal_rel_eq_height (C : cell -> bool) (h : int) (oram : oram) (ioram : ioram) :
     internal_rel C h oram ioram => oram.`height = ioram.`iheight.
   proof. by smt(). qed.

   lemma is_oram_pred0_internal_rel (h : int) (oram : oram) (ioram : ioram) :
     is_oram pred0 oram => internal_rel pred0 h oram ioram.
   admitted.

   lemma merged_filtered_bound (C : cell -> bool) (h : int) (oram : oram) (ioram : ioram) (k : int) :
        internal_rel C h oram ioram
     => (k <= let pb = ioram.`bpath in
             let bcks : block list list =
                 map (fun p => oram.`bucket p) (prefixes ioram.`bpath) in
                   count
                       (fun (b : block) => (isprefix pb b.`2))
                       (flatten bcks))
     => k <= ioram.`counters false + ioram.`counters true.
   (* TODO: Manuel *)
   admitted.

   lemma count_le ['a] (p1 p2 : 'a -> bool) (s : 'a list) :
     p1 <= p2 => count p1 s <= count p2 s.
   proof. by move=> lep; elim: s => //= x s ih; smt(). qed.

   lemma count_eq_elem ['a] (p1 p2 : 'a -> bool) (s : 'a list) :
     (forall (x : 'a), x \in s => (p1 x <=> p2 x)) => (count p1 s) = (count p2 s).
   proof.
   elim s.
   + smt().
   + move => *.
     rewrite -cat1s !count_cat /#. (* stuck when -cat1s, sounds like a bug of easycrypt *)
   qed.

   hint exact : subseq_refl.

   lemma subseq_behead ['a] (s : 'a list) : subseq (behead s) s.
   proof. by case: s => //= x s; apply: subseq_cons. qed.

   lemma subseq_trim ['a] (s : 'a list) (i : int) : subseq (trim s i) s.
   proof.
   case: (0 <= i) => [ge0_i | /ltzNge ?]; last by rewrite trim_neg.
   rewrite -{2}[s](cat_take_drop i) /trim &(cat_subseq) //.
   by rewrite -behead_drop // &(subseq_behead).
   qed.

   lemma is_ioram_height_gt0 (ioram : ioram):
       is_ioram ioram => 0 < ioram.`iheight.
   proof. by move => @/is_ioram. qed.

   lemma is_oram_block_duplicate_freeness (C: cell -> bool) (oram : oram):
         is_oram C oram =>
       (forall (p1 p2 : path) (block : block),
           C block.`1
        => block \in oram.`bucket p1
        => block \in oram.`bucket p2
        => p1 = p2).
   proof.
   move => H_is_oram p1 p2 block ?.
   by rewrite !(nthP witness) => /> * /#.
   qed.

   lemma size1 ['a] (x : 'a) :
       size [x] = 1.
   proof. apply size_eq1. exists x. done. qed.

   lemma nth1 ['a] (x : 'a) :
       nth witness [x] 0 = x.
   proof. smt(). qed.

   lemma count_nil ['a] (p : 'a -> bool) :
       count p [] = 0.
   proof. by smt(). qed.

   lemma isprefix1 ['a] (s1 : 'a list) (x : 'a) :
       isprefix s1 (s1 ++ [x]).
   proof.
   rewrite /isprefix take_cat size_cat //= cats0 => /#.
   qed.

   lemma is_ioram_bpath_ltheight (ioram : ioram):
       is_ioram ioram => (size ioram.`bpath) < (ioram.`iheight).
   proof. by move => @/is_ioram. qed.

   lemma map_mem ['a 'b] (f : 'a -> 'b) (s : 'a list) (x : 'b) :
       x \in (map f s) <=> exists (y : 'a), y \in s /\ x = (f y).
   proof. by elim s => /#. qed.

   lemma isprefix_elem ['a] (s1 s2 : 'a list) :
       isprefix s1 s2 <=> (size s1 <= size s2 /\ forall i, 0 <= i < size s1 => s1.[i] = s2.[i]).
   proof.
   rewrite /isprefix.
   split.
   + by smt(nth_take).
   + move => [#] *.
     split => //=.
     apply (eq_from_nth witness).
     + by smt(size_take List.size_ge0).
     + by smt(nth_take).
   qed.

   lemma app_isprefix ['a] (s1 s2 : 'a list) (x : 'a) :
       size s1 < size s2
    => isprefix s1 s2
    => s2.[size s1] = x
    => isprefix (s1 ++ [x]) s2.
   proof.
   rewrite /isprefix.
   move => /> ??H.
   split.
   + by smt(size_cat size1).
   + by rewrite size_cat size1 {1} H cats1 (take_nth witness) /#.
   qed.

   lemma prefixes_size ['a] (s : 'a list) :
       size (prefixes s) = size s + 1.
   proof.
   rewrite /prefixes size_map size_range ler_maxr; by smt(List.size_ge0).
   qed.

   lemma map_id_in ['a] (f : 'a -> 'a) (s : 'a list) :
      (forall x, x \in s => f x = x) => map f s = s.
   proof. by move=> *; rewrite -{2}(List.map_id s) &(eq_in_map). qed.

   lemma isprefix_size ['a] (s1 s2 : 'a list) :
      isprefix s1 s2 => size s1 <= size s2.
   proof.
   rewrite /isprefix; smt(size_take).
   qed.

   lemma prefixes_isprefix ['a] (s1 s2 : 'a list) :
       s1 \in (prefixes s2) <=> isprefix s1 s2.
   proof.
   rewrite /prefixes /isprefix.
   rewrite (nthP witness) => />.
   split.
   + move => i.
     rewrite size_map size_range lez_maxr; 1: by smt(List.size_ge0).
     move => //= *.
     rewrite (nth_map witness witness); 1: by smt(size_range List.size_ge0).
     rewrite nth_range //=.
     by smt(size_take take_take).
   + move => *.
     exists (size s1).
     rewrite size_map size_range lez_maxr; 1: by smt(List.size_ge0).
     rewrite (nth_map witness witness); 1: by smt(size_range List.size_ge0).
     rewrite nth_range //=; 1: by smt().
     by smt(size_take take_take).
   qed.

   lemma isprefix_catL ['a] (q2 q1 p : 'a list) : isprefix (q1 ++ q2) p => isprefix q1 p.
   proof.
   rewrite /isprefix => /> *.
   split.
   + by smt(size_cat List.size_ge0).
   + have ?: take (size q1) (q1 ++ q2) = q1.
     + by rewrite take_cat; smt(take0 cats0).
     have ?: take (size q1) p = take (size q1) (take (size (q1 ++ q2)) p).
     + by smt(size_cat take_take List.size_ge0).
     by smt().
   qed.

   lemma flatten_map_nil ['a 'b] (f : 'a -> 'b list) (s : 'a list) :
       (forall (x : 'a), x \in s => f x = []) => flatten (map f s) = [].
   proof.
   elim s; by smt(map_cons flatten_cons).
   qed.

   lemma take_eq_n ['a] (l1 l2 : 'a list) (n1 n2 : int) :
       0 <= n1 <= size l1
    => 0 <= n2 <= size l2
    => take n1 l1 = take n2 l2
    => n1 = n2.
   proof.
   move => *.
   have: size (take n1 l1) = size (take n2 l2) by smt().
   rewrite !size_take; by smt().
   qed.

   lemma count_seq1 ['a] (f : 'a -> bool) (x : 'a) :
       count f [x] = (b2i (f x)).
   proof. smt(). qed.

   lemma map1 ['a 'b] (f : 'a -> 'b) (x : 'a) :
       map f [x] = [f x].
   proof. smt(). qed.

   lemma contra_common_prefix ['a] (x s t : 'a list) (i : int) :
       take i s <> take i t
    => i <= size x
    => isprefix x s
    => isprefix x t
    => false.
   proof.
   move => @/isprefix *.
   have: take i (take (size x) s) = take i (take (size x) t) by smt().
   by smt(take_take).
   qed.

   lemma internal_fetch (C : cell -> bool) (h : int) (o : oram) (io : ioram) (c0 : cell) :
     equiv[ORAM.fetch ~ InternalORAM.fetch :
        arg{1} = (o, c0) /\ arg{2} = io /\ internal_rel C h o io
     ==>
        internal_rel (predI C (predC1 c0)) h res{1}.`1 res{2}
     ].
   proof.
   proc=> /=; sp.
   while {1} (
          0 <= i{1} <= oram{1}.`height + 1
     /\ pos{1} = oram{1}.`positions c{1}
     /\ c{1} = c0
     /\ internal_rel_fetch C h c0 oram{1} oram{2}
     /\ (forall _p _i, 0 <= _i < i{1} =>
                        size _p = oram{1}.`height =>
            let block = oram{1}.`bucket (take _i _p) in
              !(has (fun (block : block) => block.`1 = c0) block))
   ) (oram.`height  - i + 1){1}.
   - move => &m z; sp 3; wp 1 => /=; elim* => lkg; if; last first.
     - skip=> |> &hr 2? H_internal_rel *; do! split; 1,2,4: smt().
       move => pp ii???.
       case (ii = i{hr}); 2: by smt(size_take).
       move => Hii1; rewrite Hii1 /=.
       case (take i{hr} pp = take i{hr} (oram{hr}.`positions c0)).
       + by move => -> /=; rewrite /"_.[_<-_]" /=; smt(has_find).
       + move => Hpp.
         by rewrite hasP &(negb_exists) => //= /#.
   - auto => &hr |> h1 h2 h3 h4 h5 h6; (do! split) => /=; 1,2,3,4,5,7,8,11: by smt().
     (* is_oram_fetch *)
     + move => *;split;1: by smt(mem_trim).
       move => *;split;1: by smt().
       move => *;split;1: by smt(mem_trim).
       move => *;split.
       + move => _c0 Hc.
         rewrite /internal_rel in h3; elim h3 => |> h31 h32 h33 h34.
         rewrite /is_oram_fetch in h32; elim h32 => ? [? [? [? [He *]]]]; elim (He _c0 _);1:smt().
         move => //= ip [Hip Heip]; exists ip; split; 1:smt().
         move => Hipp /=; rewrite hasP in Heip; elim Heip => /= b' Hb.
         rewrite hasP => /=; exists b';split;2:smt().
         by smt(trim_mem).
         by smt(mem_trim find_trim_lt find_trim_ge size_trim trim_id).
     + move => b *.
       rewrite /internal_rel_fetch in h3; elim h3 => /> 11? Hb.
       apply /(ler_trans (count
            (fun (b0 : block) => isprefix (oram{m}.`bpath ++ [b]) b0.`2)
            (flatten (map oram{hr}.`bucket (prefixes oram{m}.`bpath))))); last by exact Hb.
       case: (i{hr} <= size oram{m}.`bpath) => ?.
       + rewrite /prefixes -!map_comp /(\o).
         rewrite !(range_cat (i{hr} + 1) 0 (size oram{m}.`bpath + 1)); 1,2: smt().
         rewrite !(range_cat i{hr} 0 (i{hr} + 1)); 1,2: smt().
         rewrite !map_cat !flatten_cat !count_cat.
         rewrite (_:
            (map
                (fun (x : int) =>
                oram{hr}.`bucket.[take i{hr} (oram{hr}.`positions c{hr}) <-
                    trim (oram{hr}.`bucket
                    (take i{hr} (oram{hr}.`positions c{hr})))
                    (find (fun (x0 : block) => x0.`1 = c{hr}) (oram{hr}.`bucket
                        (take i{hr} (oram{hr}.`positions c{hr}))))]
                (take x oram{m}.`bpath))
                (range (i{hr} + 1) (size oram{m}.`bpath + 1)))
          = (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`bpath))
                (range (i{hr} + 1) (size oram{m}.`bpath + 1)))
         ).
         + apply eq_in_map.
           move => x * @/"_.[_<-_]" //=.
           by smt(mem_range size_take).
         rewrite (_:
            (map
                (fun (x : int) =>
                oram{hr}.`bucket.[take i{hr} (oram{hr}.`positions c{hr}) <-
                    trim (oram{hr}.`bucket
                    (take i{hr} (oram{hr}.`positions c{hr})))
                    (find (fun (x0 : block) => x0.`1 = c{hr}) (oram{hr}.`bucket
                        (take i{hr} (oram{hr}.`positions c{hr}))))]
                (take x oram{m}.`bpath)) (range 0 i{hr}))
          = (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`bpath))
                (range 0 i{hr}))).
         + apply eq_in_map.
           move => x * @/"_.[_<-_]" //=.
           by smt(mem_range size_take).
         apply lez_add2r.
         apply lez_add2l.
         apply count_subseq.
         rewrite !rangeS !map1 !flatten1 //=.
         rewrite /"_.[_<-_]".
         case _ : (_ = _) => //=.
         + smt (subseq_trim).
       + rewrite (_:
            (map
                oram{hr}.`bucket.[take i{hr} (oram{hr}.`positions c{hr}) <-
                trim (oram{hr}.`bucket (take i{hr} (oram{hr}.`positions c{hr})))
                    (find (fun (x : block) => x.`1 = c{hr}) (oram{hr}.`bucket
                    (take i{hr} (oram{hr}.`positions c{hr}))))]
                (prefixes oram{m}.`bpath))
          = (map oram{hr}.`bucket (prefixes oram{m}.`bpath))
         ).
         + apply eq_in_map.
           move => x @/prefixes @/"_.[_<-_]" //=.
           rewrite (nthP witness) => /> => i0 ?.
           rewrite size_map.
           move => ?.
           have ?: i0 < size oram{m}.`bpath + 1.
           + by smt(size_range lez_maxr List.size_ge0).
           rewrite (nth_map witness witness) //= nth_range //=.
           have -> //=: !take i{hr} (oram{hr}.`positions c{hr}) = take i0 oram{m}.`bpath by smt(size_take).
           by apply ler_eqVlt; left; reflexivity.
     + move => pp ii???.
       case (ii = i{hr}); 2: by smt(size_take).
       move => Hii1; rewrite Hii1 /=.
       case (take i{hr} (oram{hr}.`positions c{hr}) = take i{hr} pp); 1: by
         move => -> /=; rewrite /"_.[_<-_]" /=; apply mem_uniq_triple; apply uniq_cells => /#.
       move => Hpp; rewrite  /"_.[_<-_]" Hpp /=; rewrite hasP negb_exists /= /#.
   - skip=> |> H.
     rewrite /internal_rel in H; elim H => |> ? h_is_oram h_is_ioram counting_ineq.
     rewrite /is_oram in h_is_oram; elim h_is_oram => |> ??? Hc *.
     rewrite /is_ioram in h_is_ioram; elim h_is_ioram => |> *.
     split.
     (* pre => inv *)
     do! split; 1..3,5,6,8: smt().
     + move => *. split. by assumption.
       move => *. split. by assumption.
       move => * /#.
       move: counting_ineq => />.
     (* inv => post *)
     move => /> i_L oram_L *; (do! split).
     + by move => * /#.
     + move => 16? H_counting_ineq_L Hnc; split.
       + move => ??? pp ? bb.
         + have := Hnc (pp++nseq (oram_L.`height - size pp) false) (size pp) _ _;1,2: smt(size_cat size_nseq List.size_ge0).
           by rewrite hasPn;smt(take_size_cat).
       + by exact H_counting_ineq_L.
   qed.

   lemma internal_flush (_C : cell -> bool) (_h : int) (_oram : oram) (_ioram : ioram) :
     equiv[ORAM.flush ~ InternalORAM.flush :
          arg{1} = _oram
       /\ arg{2} = _ioram
       /\ internal_rel _C _h arg{1} arg{2}
       ==>
          internal_rel _C _h res{1} res{2}
   ].
   proof.
   proc => /=.
   seq 1 1: (
       ={p} /\ (size p{1}) = oram{1}.`height
     /\ (internal_rel _C _h oram{1} oram{2})
     /\ oram{1} = _oram /\ oram{2} = _ioram
   ).
   + rnd (fun x => x) => />.
     + by move => &1 &2 /> 14? //=.
     + auto => |> H_internal_rel *.
       have-> //=: _oram.`height = _ioram.`iheight by smt(internal_rel_eq_height).
       + move => *; split => * //=.
         by smt(supp_dlist_size).
   sp 2 1.
   seq 1 0: (
       ={p}
     /\ (size p{1}) = oram{1}.`height
     /\ b{2} = p{2}.[size oram{2}.`bpath]
     /\ i{1} = oram{1}.`height + 1
     /\ internal_rel _C _h oram{1} oram{2}
     /\ ((isprefix oram{2}.`bpath p{2}) => (
        (* count the blocks along bpath that will be flushed, which is 0 *)
            let b = p{2}.[size oram{2}.`bpath] in
            let pb = oram{2}.`bpath ++ [b] in
            (let bcks : block list = flatten (map (fun p => oram{1}.`bucket p) (prefixes oram{2}.`bpath)) in
                 count (fun (b : block) => (isprefix pb b.`2)) bcks = 0)))
   ).

   while {1} (
        0 <= i{1} <= oram{1}.`height + 1
     /\ ={p}
     /\ (size p{1}) = oram{1}.`height
     /\ oram{1}.`height = _oram.`height
     /\ oram{1}.`positions = _oram.`positions
     /\ oram{2} = _ioram
     /\ oram{1}.`height = oram{2}.`iheight
     /\ internal_rel _C _h _oram _ioram
     /\ internal_rel (predI _C (fun cc => size pushed{1} <= find (fun (b : block) => b.`1 = cc) pushed{1})) _h oram{1} oram{2}
     (* Whatever is in current oram first levels is not in pushed and it was somewhere above in the original _oram *)
     /\ (forall _p, size _p < i{1} =>
          (all (fun (block : block) =>
            !block \in pushed{1} /\
             (exists ii, 0<= ii <= size _p /\ block \in _oram.`bucket (take ii _p))) (oram{1}.`bucket _p)))
     (* Whatever is in current oram later levels is untouched from _oram *)
     /\ (forall _p, i{1} <= size _p <= oram{1}.`height => oram{1}.`bucket _p = _oram.`bucket _p)
     (* block is in pushed iff it was higher up in the path of _oram, agress on the flushing path p, and it's not in the higher path of the current oram *)
     /\ (forall bb, bb \in pushed{1} <=>
             (i{1} <= _oram.`height
           /\ take i{1} bb.`2 = take i{1} p{1}
           /\ (exists ii, 0 <= ii < i{1} /\ bb \in _oram.`bucket (take ii p{1}))))
           (* /\ (forall (ii : int) (p : path), 0 <= ii < i{1} /\ !(bb \in oram{1}.`bucket (take ii p))))) *)
     (* we have no repeats in pushed *)
     /\ (forall i1 i2,
             0 <= i1 < size pushed{1}
           => 0 <= i2 < size pushed{1}
           => pushed{1}.[i1].`1 = pushed{1}.[i2].`1
           => i1 = i2)
     (* count the blocks accessed that possibly go into the other subtree, which is bounded by a counter *)
     /\ (forall (b : bool),
            let pb = oram{2}.`bpath ++ [b] in
            let bcks : block list = flatten (map (fun path => oram{1}.`bucket path) (prefixes oram{2}.`bpath)) in
                count
                   (fun (b : block) => (isprefix pb b.`2))
                   (bcks ++ (if i{1} <= size oram{2}.`bpath then pushed{1} else []))
                <= oram{2}.`counters b)
     (* count the blocks accessed that will be flushed, which is 0 *)
     /\ ((isprefix oram{2}.`bpath p{1}) =>
           (let b = p{2}.[size oram{2}.`bpath] in
            let pb = oram{2}.`bpath ++ [b] in
            let bcks : block list =
              flatten
                (map
                  oram{1}.`bucket
                  (if (0 < i{1}) then (prefixes (take (i{1} - 1) oram{2}.`bpath)) else [])) in
              count (fun (b : block) => (isprefix pb b.`2)) bcks = 0))
   ) (oram.`height - i + 1){1}.
   + auto => /= |> &hr ?????? Hrel1 Hrel2 H1 H2 H3 H4 H_loop_inv1 H_loop_inv2 *.
     rewrite /internal_rel in Hrel1; elim Hrel1 => |> ? H_is_oram1 H_is_ioram1 counter_ineq_original.
     rewrite /is_oram in H_is_oram1; elim H_is_oram1 => |> ???? Hbase Hinjb Hps.
     rewrite /internal_rel in Hrel2; elim Hrel2 => |> ?? H_is_oram2 H_is_ioram2 counter_ineq.
     rewrite /is_oram in H_is_oram2; elim H_is_oram2 => |> ???? H0 ? H01 *.

     pose newpushed := (if i{hr} = oram{hr}.`height then []
         else
           filter
             (fun (block : block) =>
                take (i{hr} + 1) block.`2 = take (i{hr} + 1) p{m})
             (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m}))).
     pose stayhere := if i{hr} = oram{hr}.`height then
                  pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})
                else
                  filter
                    (fun (block : block) =>
                       take (i{hr} + 1) block.`2 <> take (i{hr} + 1) p{m})
                    (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})).
     (* setting the ground *)
     have ? : forall b, (!b \in newpushed /\ !b \in stayhere) => !b \in pushed{hr}.
     + case (i{hr} = oram{hr}.`height); 1: by smt(mem_cat).
       by rewrite /newpushed /stayhere => ->b /=; rewrite !mem_filter !mem_cat /#.

     have ? : forall b, b \in stayhere => !b \in pushed{hr} => b \in oram{hr}.`bucket (take i{hr} p{m}).
     + rewrite /stayhere;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
        by move => b;rewrite !mem_filter !mem_cat /#.

     have H_newpushed_not_pushed : forall b, b \in newpushed => !b \in pushed{hr} => b \in oram{hr}.`bucket (take i{hr} p{m}).
     + rewrite /newpushed;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
        by move => b;rewrite !mem_filter !mem_cat /#.

     have ? : forall b, b \in stayhere => !b \in newpushed.
     + rewrite /stayhere /newpushed;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
        by move => b;rewrite !mem_filter !mem_cat /#.

     have ? : forall b, !b \in stayhere => !b \in newpushed => !b \in oram{hr}.`bucket (take i{hr} p{m}).
     + rewrite /stayhere /newpushed;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
        by move => b;rewrite !mem_filter !mem_cat /#.

     have ?: forall bb1 bb2, bb1 \in stayhere => bb2 \in newpushed => bb1.`2 <> bb2.`2.
     + rewrite /stayhere /newpushed => bb1 bb2.
       case (i{hr} = oram{hr}.`height) => ? //.
       by rewrite !mem_filter //= /#.

     have Hsep : forall bb pp, size pp <= oram{hr}.`height =>
          bb \in oram{hr}.`bucket.[take i{hr} p{m} <- stayhere] pp =>
           size newpushed <= find (fun (b : block) => b.`1 = bb.`1) newpushed.
     + move => bb pp ??.
       have [ _ Hin]  := find_rng_in newpushed (fun (b : block) => b.`1 = bb.`1).
       rewrite implybE in Hin;elim Hin;1: by smt(find_ge0).
       rewrite hasP=> Hex;elim Hex => b2 /= *.
       case (b2 \in stayhere) => *; 1: by smt().
       case (i{hr} < size pp) => *.  (* block is below *)
        + have ? : bb \in _oram.`bucket pp by smt(size_take).
          pose i1 := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket pp).
          have i1b := find_rng_in (_oram.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
          case (b2 \in pushed{hr}) => Hb2.
            + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i2' p{m})).
              have := Hinjb (take i2' p{m}) pp i2f i1 _ _ _;2,4:smt(size_take nth_find mem_nth).
              + have := (find_rng_in (_oram.`bucket (take i2' p{m})) (fun (bf : block) => bf.`1 = b2.`1));1: by rewrite hasP; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i2' p{m})) _;1: by rewrite ?
hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _;rewrite ?
hasP /=; smt().
          have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
          pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})).
          have := Hinjb (take i{hr} p{m}) pp i2f i1 _ _ _.
          + have := find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
          + smt().
          + have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})) _;1: by rewrite hasP /=; smt().
            have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _; by rewrite ?hasP /=; smt().
          smt(size_take).

        case (size pp < i{hr}) => *.
        (* block is above *)
        + have ? : pp <> take i{hr} p{m} by smt(size_take).
          move : (H1 pp _); 1: by smt().
          rewrite allP => /> Hbs; move : (Hbs bb _);1:smt().
          move =>  [#? Hex];elim Hex => i1' *.
          have ? : bb \in _oram.`bucket (take i1' pp) by smt().
          pose i1f := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket (take i1' pp)).
          case (b2 \in pushed{hr}) => Hb2.
            + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i2' p{m})).
              have := Hinjb (take i2' p{m}) (take i1' pp) i2f i1f _ _ _; 4:  by smt().
              + have := find_rng_in (_oram.`bucket (take i2' p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
              + have := find_rng_in (_oram.`bucket (take i1' pp)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
              + have /= ? := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i2' p{m})) _; 1: by rewrite ?hasP /#.
                rewrite /"_.[_]" &(eq_trans _ bb.`1).
                + smt().
                + rewrite /i1f &(eq_sym_imp).
                  apply (nth_find witness (fun (b0 : block) => b0.`1 = bb.`1) (_oram.`bucket (take i1' pp))).
                  apply List.hasP.
                  by exists bb => //=.

            + have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})).
              have := Hinjb (take i{hr} p{m}) (take i1' pp) i2f i1f _ _ _;4:smt(size_take).
              + have := find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = b2.`1); 1: by rewrite hasP /#.
              + have := find_rng_in (_oram.`bucket (take i1' pp)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
              + have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})) _;1: by rewrite ?hasP;smt(nth_find).
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket (take i1' pp)) _; by rewrite ?hasP /=; smt().

        + (* block is at this level *)
          case (pp = take i{hr} p{m}) => *; last first.
          + have Hinn : bb \in _oram.`bucket pp by smt().
          pose i1 := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket pp).
          have i1b := find_rng_in (_oram.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
          case (b2 \in pushed{hr}) => Hb2.
            + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i2' p{m})).
              have := Hinjb (take i2' p{m}) pp i2f i1 _ _ _;2,4:smt(size_take).
              + have := find_rng_in (_oram.`bucket (take i2' p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i2' p{m})) _;1: by rewrite ?hasP;smt(nth_find).
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _; by rewrite ?hasP /=; smt().

            have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
            pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})).
            have := Hinjb (take i{hr} p{m}) pp i2f i1 _ _ _;2,4:smt(size_take).
            + have := find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
            + have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})) _;1: by rewrite ?hasP /=; smt().
            have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _; by rewrite ?hasP /=; smt().

        + have ? : bb \in stayhere;1: by smt().
          case (bb \in pushed{hr}) => Hpps;last first.
          +  have ? : bb \in (_oram.`bucket pp) by smt().
             pose i1 := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket pp).
             have i1b := find_rng_in (_oram.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
             case (b2 \in pushed{hr}) => Hb2.
              + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
                pose i2f := find (fun (b : block) => b.`1 = b2.`1) (_oram.`bucket (take i2' p{m})).
                have := Hinjb (take i2' p{m}) pp i2f i1 _ _ _;2,4:smt().
                + have := find_rng_in (_oram.`bucket (take i2' p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
                have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i2' p{m})) _;1: by rewrite ?hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (_oram.`bucket pp) _; by rewrite ?hasP /=; smt().

             have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt().
             pose i2f := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket (take i{hr} p{m})).
             have := Hinjb (take i{hr} p{m}) pp i2f i1 _ _ _; 2, 4: smt().
             + by have := find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
             + by have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (_oram.`bucket (take i{hr} p{m})) _; by rewrite ?hasP /=; smt().

             case (b2 \in pushed{hr}) => Hb2.
              + pose i1f := find (pred1 bb) pushed{hr}.
                pose i2f := find (pred1 b2) pushed{hr}.
                move : (H4 i1f i2f) ; smt().

             move : (H3 bb);rewrite Hpps /= => [#?? Hex];elim Hex => i1' *.
             pose i1f := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket (take i1' p{m})).
             have ? : b2 \in _oram.`bucket (take i{hr} p{m}) by smt().
             pose i2f := find (fun (b : block) => b.`1 = bb.`1) (_oram.`bucket (take i{hr} p{m})).
             have := Hinjb (take i{hr} p{m}) (take i1' p{m}) i2f i1f _ _ _;3..:smt().
             + have := find_rng_in (_oram.`bucket (take i{hr} p{m})) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
             + have := find_rng_in (_oram.`bucket (take i1' p{m})) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().

       have Hinjf : forall bb1 bb2 pp1 pp2, bb1 \in _oram.`bucket pp1 => bb2 \in _oram.`bucket pp2 =>
                 bb1.`1 = bb2.`1 => pp1 <> pp2 => false.
         move => bb1 bb2 pp1 pp2 Hl1 Hl2 Hl3 Hl4.
         pose i1f := find (fun (bf : block) => bf.`1 = bb1.`1) (_oram.`bucket pp1).
         pose i2f := find (fun (bf : block) => bf.`1 = bb2.`1) (_oram.`bucket pp2).
         have := Hinjb pp1 pp2 i1f i2f _ _ _.
              + have := find_rng_in (_oram.`bucket pp1) (fun (bf : block) => bf.`1 = bb1.`1); rewrite hasP; smt().
              + have := find_rng_in (_oram.`bucket pp2) (fun (bf : block) => bf.`1 = bb2.`1); rewrite hasP; smt().
                have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb1.`1)(_oram.`bucket pp1)_;1: by rewrite ?hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb2.`1) (_oram.`bucket pp2)  _; by rewrite ?hasP /=; smt().
              by smt(size_take).

     (* pushed{hr} + bucket (take i{hr} p{m}) = stayhere + newpushed *)
     have ?: forall b, (b \in pushed{hr} \/ b \in (oram{hr}.`bucket (take i{hr} p{m}))) <=> (b \in stayhere \/ b \in newpushed).
     + smt().

     (* pushed{hr} /\ bucket (take i{hr} p{m}) = \emptyset *)
     (* have ?: forall b, (b \in pushed{hr}) => !b \in (oram{hr}.`bucket (take i{hr} p{m})). *)
     (* + smt(). *)

     (* stayhere /\ newpushed = \emptyset *)
     have ?: forall b, (b \in stayhere) => !(b \in newpushed).
     + smt().

     have ?: perm_eq (pushed{hr} ++ (oram{hr}.`bucket (take i{hr} p{m}))) (stayhere ++ newpushed).
     + rewrite /stayhere /newpushed.
       case: (i{hr} = oram{hr}.`height) => ?.
       + rewrite cats0 perm_eq_refl //=.
       + rewrite (_:
            (fun (block : block) =>
                take (i{hr} + 1) block.`2 = take (i{hr} + 1) p{m})
          = predC
                (fun (block : block) =>
                    take (i{hr} + 1) block.`2 <> take (i{hr} + 1) p{m})).
         + rewrite /predC //=.
         rewrite perm_eq_sym perm_filterC.

     (* have ? : uniq (prefixes oram{m}.`bpath). *)
     (* + rewrite /prefixes nth_uniq => i0 j0. *)
     (*   rewrite size_map size_range lez_maxr => *; 1: by smt(List.size_ge0). *)
     (*   rewrite !(nth_map witness witness) => />; 1,2: by smt(size_map size_range List.size_ge0). *)
     (*   rewrite !nth_range //=. *)
     (*   by smt(size_take). *)

     (* have ? : uniq (oram{hr}.`bucket (take i{hr} p{m}) ++ pushed{hr}). *)
     (* + apply nth_uniq => i0 j0. *)
     (*   by rewrite size_cat !nth_cat /#. *)

     (* have ?: uniq (stayhere ++ newpushed). *)
     (* + rewrite /stayhere /newpushed. *)
     (*   case: (i{hr} = oram{hr}.`height). *)
     (*   + by rewrite cats0 uniq_catC //=. *)
     (*   + move => ?. *)
     (*     apply cat_uniq; do! split. *)
     (*     + by rewrite &(filter_uniq) uniq_catC //=. *)
     (*     + rewrite hasPn => x. *)
     (*       by rewrite !mem_filter //= /#. *)
     (*     + by rewrite &(filter_uniq) uniq_catC //=. *)

     have H_map_small:
        (map
            (fun (x : int) =>
            if take i{hr} p{m} = take x oram{m}.`bpath then stayhere
            else oram{hr}.`bucket (take x oram{m}.`bpath)) (range 0 i{hr}))
      =
        (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`bpath)) (range 0 i{hr})).
     + apply eq_in_map => x />.
       rewrite mem_range => ?.
       by have-> //: !take i{hr} p{m} = take x oram{m}.`bpath by smt(size_take).

     have H_map_large:
        (map
            (fun (x : int) =>
                if take i{hr} p{m} = take x oram{m}.`bpath then stayhere
                else oram{hr}.`bucket (take x oram{m}.`bpath))
            (range (i{hr} + 1) (size oram{m}.`bpath + 1)))
        = (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`bpath))
            (range (i{hr} + 1) (size oram{m}.`bpath + 1))).
     + apply eq_in_map => x />.
       rewrite mem_range => ?.
       by have-> //: !take i{hr} p{m} = take x oram{m}.`bpath by smt(size_take).

     (* main proof started *)
     (* let's prove loop_inv1 first, because is_oram is a corollary of this. *)
     have H_new_loop_inv1:
        forall (b0 : bool),
        count
            (fun (b1 : block) => isprefix (oram{m}.`bpath ++ [b0]) b1.`2)
            (flatten
                (map oram{hr}.`bucket.[take i{hr} p{m} <- stayhere]
                    (prefixes oram{m}.`bpath))
            ++ (if (i{hr} + 1 <= size oram{m}.`bpath) then newpushed else [])) <=
        oram{m}.`counters b0.
     + move => b @/"_.[_<-_]" />.
       case (isprefix oram{m}.`bpath p{m}) => Hpre.
       + case (i{hr} < size oram{m}.`bpath) => ?.
         (* the nodes up to i have equivalent or less blocks, while other nodes remain the same. *)
         (* We will specifically seperate the current node: stayhere, and prove that it's no more than the blocks in pushed and node i before *)
         have Hi: (i{hr} <= size oram{m}.`bpath) by smt().
         have->: (i{hr} + 1 <= size oram{m}.`bpath) by smt().
         move: H_loop_inv1 => H_loop_inv1.
         rewrite Hi //= in H_loop_inv1.
         have Htake: take i{hr} oram{m}.`bpath = take i{hr} p{m}.
         + rewrite /isprefix in Hpre.
           elim Hpre => ? H.
           rewrite H take_take /#.
         have Hheight: !i{hr} = oram{hr}.`height by smt().
         apply (ler_trans
           (count
             (fun (b1 : block) => isprefix (oram{m}.`bpath ++ [b]) b1.`2)
             (flatten (map oram{hr}.`bucket (prefixes oram{m}.`bpath)) ++
               pushed{hr}))); last by exact H_loop_inv1.
         rewrite /prefixes -!map_comp /(\o).
         rewrite (range_cat i{hr}); 1,2: by smt().
         rewrite (range_cat (i{hr} + 1) i{hr}); 1,2: by smt().
         rewrite rangeS !map_cat !flatten_cat !count_cat.
         rewrite !map1 !flatten_seq1 //=.
         rewrite !Htake //= H_map_small H_map_large.
         have ?:
            count
                (fun (b1 : block) => isprefix (oram{m}.`bpath ++ [b]) b1.`2)
                stayhere
          + count
                (fun (b1 : block) => isprefix (oram{m}.`bpath ++ [b]) b1.`2)
                newpushed
          = count
                (fun (b1 : block) => isprefix (oram{m}.`bpath ++ [b]) b1.`2)
                (oram{hr}.`bucket (take i{hr} p{m}))
          + count
                (fun (b1 : block) => isprefix (oram{m}.`bpath ++ [b]) b1.`2)
                pushed{hr}.
         + by rewrite -!count_cat &(perm_eqP) perm_eq_sym perm_catCl //=.
         by smt().

         case: (i{hr} = size oram{m}.`bpath) => Hi.
         (* The current iteration i is exactly at bpath. *)
         + have-> /=: !(i{hr} + 1 <= size oram{m}.`bpath) by smt().
           rewrite cats0.
           move: H_loop_inv1.
           have-> /=: (i{hr} <= size oram{m}.`bpath) by smt().
           move => H_loop_inv1.
           apply (ler_trans
               (count
                 (fun (b1 : block) =>
                    isprefix (oram{m}.`bpath ++ [b]) b1.`2)
                 (flatten (map oram{hr}.`bucket (prefixes oram{m}.`bpath)) ++
                  pushed{hr}))
           ).
           + rewrite count_cat.
             rewrite /prefixes -!map_comp /(\o).
             rewrite (range_cat i{hr}); 1,2: by smt().
             rewrite -Hi rangeS !map_cat !flatten_cat !count_cat.
             rewrite !map1 !flatten_seq1 /=.
             have-> //=: take i{hr} oram{m}.`bpath = take i{hr} p{m} by smt(take_take).
             rewrite H_map_small -addzA lez_add2l -count_cat.
             apply (ler_trans (
                count
                    (fun (b1 : block) => isprefix (oram{m}.`bpath ++ [b]) b1.`2)
                    (stayhere ++ newpushed)
             )).
             + by smt(count_cat count_ge0).
             + apply ler_eqVlt; left.
               rewrite &(perm_eqP) perm_eq_sym {1} perm_catCl //=.
           by exact H_loop_inv1.

         (* The current iteration i goes over bpath, then we can simply apply the loop invariant 1. *)
         + move: H_loop_inv1.
           rewrite (_: (!i{hr} <= size oram{m}.`bpath)); 1: by smt().
           rewrite (_: (!i{hr} + 1 <= size oram{m}.`bpath)); 1: by smt().
           rewrite //= !cats0.
           move => H_loop_inv1.
           have->:
              (map
                  (fun (x' : path) =>
                      if take i{hr} p{m} = x' then stayhere else oram{hr}.`bucket x')
                  (prefixes oram{m}.`bpath))
            = (map
                  oram{hr}.`bucket
                  (prefixes oram{m}.`bpath)).
           + apply eq_in_map.
             move => /> x *.
             rewrite (_: take i{hr} p{m} <> x); last by smt().
             + apply (contraNneq false) => *; last by done.
               have H_size_eq: (size (take i{hr} p{m})) = size x by smt().
               have H_size_x_small: size x <= size oram{m}.`bpath by smt(prefixes_isprefix isprefix_size).
               have H_size_larger: (size (take i{hr} p{m})) = min i{hr} (size p{m}) by smt(size_take).
               by smt().
             by exact H_loop_inv1.

       (* The number of blocks along bpath is not increasing. *)
       (* We will split the case according whether i falls in the common prefix of bpath and p. *)
       + apply (ler_trans (count
                    (fun (b0 : block) =>
                        isprefix (oram{m}.`bpath ++ [b]) b0.`2)
                    (flatten (map oram{hr}.`bucket (prefixes oram{m}.`bpath)) ++
                    if i{hr} <= size oram{m}.`bpath then pushed{hr} else []))); last by exact H_loop_inv1.
         + case: (take i{hr} p{m} = take i{hr} oram{m}.`bpath) => Htake.
           have ?: i{hr} < size oram{m}.`bpath by smt(size_take take_oversize).
           rewrite (_: i{hr} <= size oram{m}.`bpath) //=; 1: by smt().
           rewrite (_: i{hr} + 1 <= size oram{m}.`bpath) //=; 1: by smt().
           have Hheight: !(i{hr} = oram{hr}.`height) by smt().
           apply ler_eqVlt; left.
           apply perm_eqP.
           rewrite /prefixes -!map_comp /(\o).
           rewrite (range_cat i{hr}); 1,2: by smt().
           rewrite (range_cat (i{hr} + 1) i{hr}); 1,2: by smt().
           rewrite rangeS.
           rewrite !map_cat !flatten_cat.
           rewrite H_map_small H_map_large.
           rewrite !map1 !flatten_seq1 Htake //=.
           rewrite -(catA
                (flatten
                    (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`bpath))
                        (range 0 i{hr})))
                (stayhere ++
                    flatten
                    (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`bpath))
                        (range (i{hr} + 1) (size oram{m}.`bpath + 1))))
                newpushed
           ).
           rewrite -(catA
                (flatten
                    (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`bpath))
                        (range 0 i{hr})))
                (oram{hr}.`bucket (take i{hr} oram{m}.`bpath) ++
                    flatten
                    (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`bpath))
                        (range (i{hr} + 1) (size oram{m}.`bpath + 1))))
                pushed{hr}
           ).
           rewrite perm_cat2l.
           rewrite perm_catAC perm_eq_sym perm_catAC.
           rewrite perm_cat2r.
           rewrite perm_catCl.
           by rewrite -Htake //=.
         + have->:
              (map
                  (fun (x' : path) =>
                      if take i{hr} p{m} = x' then stayhere else oram{hr}.`bucket x')
                  (prefixes oram{m}.`bpath)) =
              (map
                  (fun (x' : path) => oram{hr}.`bucket x')
                  (prefixes oram{m}.`bpath)).
           + apply eq_in_map => @/prefixes /> x.
             rewrite mapP.
             elim => x0 [#].
             rewrite mem_range => //= *.
             have ?: size x = x0.
             + rewrite (_: x0 = size (take x0 oram{m}.`bpath)); by smt(size_take).
             case: (take i{hr} p{m} = x) => H.
             + have ?: size x = i{hr}.
               + rewrite (_: i{hr} = size (take i{hr} p{m})); by smt(size_take).
               by smt().
             + by trivial.
           rewrite !count_cat &(ler_add2l).
           apply ler_eqVlt; left.
           have ?:
             count
                (fun (b1 : block) => isprefix (oram{m}.`bpath ++ [b]) b1.`2)
                (if i{hr} + 1 <= size oram{m}.`bpath then newpushed else []) = 0.
           + case: (i{hr} + 1 <= size oram{m}.`bpath) => ?.
             + rewrite /newpushed.
               have-> /=: !i{hr} = oram{hr}.`height by smt().
               rewrite count_filter /predI.
               apply count_eq0.
               apply hasPn => x * //=.
               apply negP => [#] *.
               apply (contra_common_prefix (take (i{hr} + 1) x.`2) x.`2 p{m} i{hr}).
               + by smt(isprefix_catL take_take).
               + by smt(size_take).
               + by smt(size_take).
               + by smt(size_take).
             + by done.
           have ?:
             count
                (fun (b0 : block) => isprefix (oram{m}.`bpath ++ [b]) b0.`2)
                (if i{hr} <= size oram{m}.`bpath then pushed{hr} else []) = 0.
           + case: (i{hr} <= size oram{m}.`bpath) => ?.
             + apply count_eq0.
               apply hasPn => x * //=.
               apply negP => [#] *.
               apply (contra_common_prefix (take i{hr} x.`2) x.`2 p{m} i{hr}).
               + by smt(isprefix_catL take_take).
               + by smt(size_take).
               + by smt(size_take).
               + rewrite /isprefix size_take; smt().
           by smt().
        by smt().

     do! split; 1,2,3,4,5,7,8: by smt().
     (* is oram *)
     + move=> *; split.
       + move => //= @/"_.[_<-_]" p0 ?.
         have -> /=: !take i{hr} p{m} = p0 by smt(size_take).
         by smt().
       move=> /> *; split.
       + move => pp ? bb Hbb; split;1: by
         case (i{hr} < size pp) => *;
         case (size pp < i{hr}) => *;smt().
       (* it remains to show not in newpushed *)
       by apply (Hsep bb pp).

       move=> /> *; split.
       + move => c Hc Hnh.
         case (size stayhere <= find (fun (b : block) => b.`1 = c) stayhere) => Hcs; last first.
         + (* storing it now: it's in stayhere *)
           exists i{hr}; split => *;1:smt().
           have  := find_rng_in stayhere (fun (b : block) => b.`1 = c). (* Question. *)
           have -> /= : 0 <= find (fun (b : block) => b.`1 = c) stayhere < size stayhere
                by smt(List.size_ge0 find_ge0).
           rewrite hasP => Hex; elim Hex => bb *.
           rewrite hasP; exists bb.
           by case (bb \in pushed{hr}) => Hip; by move : (Hps p{m} _ i{hr} _);smt().
          + (* already in tree *)
            move : (H0 c _).
            + rewrite /predI /=;split;1:smt().
              have  := find_rng_out stayhere (fun (b : block) => b.`1 = c).
              have  := find_rng_out newpushed (fun (b : block) => b.`1 = c).
              have  := find_rng_out pushed{hr} (fun (b : block) => b.`1 = c).
              rewrite !hasP !negb_exists //=.
              smt().
            move => H0c; elim H0c => i' [#?? Hb]; exists i';do split;1,2:smt().
            rewrite hasP in Hb; elim Hb => bb /= *.
            rewrite hasP; exists bb => /=.
            case (i' < i{hr}) => *; 1: by smt(size_take). (* block is below *)
            case (i{hr} = i') => *; last by smt(size_take).
            + have ? : take i{hr} p{m} <> (take i' (oram{hr}.`positions c)); last by smt().
              have  := find_rng_out stayhere (fun (b : block) => b.`1 = c).
              have  := find_rng_out newpushed (fun (b : block) => b.`1 = c).
              have  := find_rng_out (oram{hr}.`bucket (take (i{hr}) p{m})) (fun (b : block) => b.`1 = c).
              rewrite !hasP !negb_exists /=.
              have -> /= : ! find (fun (b : block) => b.`1 = c) newpushed < size newpushed by smt().
              have -> /= : ! find (fun (b : block) => b.`1 = c) stayhere < size stayhere by smt().
              move => Hib Hinp Hish; move : (Hinp bb); move : (Hish bb); rewrite  (: bb.`1 = c) 1:/# /=.
              by smt().

       + move => /> *; split.
         move => /> p1 p2 i1 i2 ????.
         (* begin injectivity *)
         rewrite /"_.[_<-_]".
         case (take i{hr} p{m} = p1);
         case (take i{hr} p{m} = p2) => ??; last by smt().
         + rewrite /stayhere; case (i{hr} = oram{hr}.`height) => ?.
           + rewrite /"_.[_]" !nth_cat.
             case (i1 < size pushed{hr}); case (i2 < size pushed{hr}) => ??;1,4 : smt(size_cat size_filter List.size_ge0).
             + move => ?; pose b1 := nth witness pushed{hr} i1.
               pose b2 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (i2 - size pushed{hr}).
               have Hb1 : b1 \in pushed{hr} by smt(mem_nth).
               have Hb2 : b2 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
               by smt(size_take).
             + move => ?; pose b2 := nth witness pushed{hr} i2.
               pose b1 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (i1 - size pushed{hr}).
               have Hb2 : b2 \in pushed{hr} by smt(mem_nth).
               have Hb1 : b1 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
               smt(size_take).

           + have /= HH := (filter_inj
                   (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m}))
                   (fun (b : block) => b.`1)
                   (fun (block : block) => take (i{hr} + 1) block.`2 <> take (i{hr} + 1) p{m})).
             have ? : (forall (i1 i2 : int),
               0 <= i1 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) =>
               0 <= i2 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) =>
                  (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) i1).`1 =
                  (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) i2).`1 =>
                     i1 = i2) ; last by smt().
             move => ii1 ii2 ??.
             rewrite /"_.[_]" !nth_cat.
             case (ii1 < size pushed{hr}); case (ii2 < size pushed{hr}) => ??;1,4:smt(size_cat size_filter List.size_ge0).
             + move => ?; pose b1 := nth witness pushed{hr} ii1.
               pose b2 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (ii2 - size pushed{hr}).
               have Hb1 : b1 \in pushed{hr} by smt(mem_nth).
               have Hb2 : b2 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(mem_nth size_cat size_filter List.size_ge0).
               by smt(size_take).

             + move => ?; pose b2 := nth witness pushed{hr} ii2.
               pose b1 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (ii1 - size pushed{hr}).
               have Hb2 : b2 \in pushed{hr} by smt(mem_nth).
               have Hb1 : b1 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
               by smt(size_take).

         + pose b1 := stayhere.[i1].
           pose b2 := (oram{hr}.`bucket p2).[i2].
           move => ?.
           have Hb2 : b2 \in oram{hr}.`bucket p2 by smt(mem_nth).
           have  : b1 \in stayhere by smt(mem_nth).
           rewrite /stayhere => ?.
           case (b1 \in pushed{hr}) => Hb1.
           + have := H3 b1; rewrite Hb1 /= => [#?? Hex];elim Hex => i1' *.
             case (i{hr} < size p2) => *.
             + have ? : b2 \in _oram.`bucket p2 by smt(mem_nth).
               by smt(size_take).

             case (i{hr} = size p2) => *.
             + have ? : b2 \in _oram.`bucket p2 by smt(mem_nth).
               by smt(size_take).

             + have := H1 p2 _;1:smt().
               rewrite allP => H1p2; move : (H1p2 b2 _) => /=;1:smt().
               move => [#? Hex];elim Hex => i2' *.
               by smt(size_take).

           + have Hbb1 : b1 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
             case (i{hr} < size p2) => *.
             + have Hbb2 : b2 \in _oram.`bucket p2 by smt(mem_nth).
               by smt(size_take).
             case (i{hr} = size p2) => *.
             + have Hbb2 : b2 \in _oram.`bucket p2 by smt(mem_nth).
               by smt(size_take).
             + have := H1 p2 _;1:smt().
               rewrite allP => H1p2; move : (H1p2 b2 _) => /=;1:smt().
               move => [#? Hex];elim Hex => i2' *.
               by smt(size_take).

         + pose b2 := stayhere.[i2].
           pose b1 := (oram{hr}.`bucket p1).[i1].
           move => ?.
           have Hb1 : b1 \in oram{hr}.`bucket p1 by smt(mem_nth).
           have  : b2 \in stayhere by smt(mem_nth).
           rewrite /stayhere => ?.
           case (b2 \in pushed{hr}) => Hb2.
           + have := H3 b2; rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
             case (i{hr} < size p1) => *.
             + have ? : b1 \in _oram.`bucket p1 by smt(mem_nth).
               by smt(size_take).
             case (i{hr} = size p1) => *.
             + have ? : b1 \in _oram.`bucket p1 by smt(mem_nth).
               by smt(size_take).
             + have := H1 p1 _;1:smt().
               rewrite allP => H1p1; move : (H1p1 b1 _) => /=;1:smt().
               move => [#? Hex];elim Hex => i1' *.
               by smt(size_take).
           + have Hbb2 : b2 \in _oram.`bucket (take i{hr} p{m}) by smt(size_take).
             case (i{hr} < size p1) => *.
             + have Hbb1 : b1 \in _oram.`bucket p1 by smt(mem_nth).
               by smt(size_take).
             case (i{hr} = size p1) => *.
             + have Hbb1 : b1 \in _oram.`bucket p1 by smt(size_take).
               by smt(size_take).
             + have := H1 p1 _;1:smt().
               rewrite allP => H1p1; move : (H1p1 b1 _) => /=;1:smt().
               move => [#? Hex];elim Hex => i1' *.
               by smt(size_take).
       (* end injectivity*)

       + move => ? pp Hpp ii ?? bb Hbb.
         case (size (take ii pp) <= i{hr}) => *; last first.
         + (* bb is below *)
           have ?: bb \in oram{hr}.`bucket (take ii pp) by smt(size_take).
           move : (H2 (take ii pp) _); 1:smt().
           move : (Hps pp _ ii _); smt(size_take).
         case (size (take ii pp) < i{hr}) => *.
         + (* bb is above *)
           have ?: bb \in oram{hr}.`bucket (take ii pp) by smt(size_take).
           move : (H01 pp _ ii _ bb _); smt(size_take).
         (* bb is at level i{hr} *)
         case (take i{hr} p{m} = take i{hr} pp) => *; last first.
         + (* other path *)
           have ?: bb \in _oram.`bucket (take ii pp);  by smt(take_oversize size_take).
           move : (Hps pp _ ii _);smt(size_take).
         (* this path *)
     (* is ioram *)
     + move => b />.
       apply (ler_trans (
         count
            (fun (b0 : block) =>
                isprefix (oram{m}.`bpath ++ [b]) b0.`2)
            (flatten
                (map oram{hr}.`bucket.[take i{hr} p{m} <- stayhere]
                    (prefixes oram{m}.`bpath)) ++
                if i{hr} + 1 <= size oram{m}.`bpath then newpushed
                else []))).
       + by smt(count_le count_cat count_ge0).
       + by exact H_new_loop_inv1.

     (* loop invariants *)
     + move => pp ?; rewrite allP => bb Hbb /=; split;last first.
       (* basic properties *)
       case (size pp < i{hr}) => Hsp.
       + move : Hbb (H1 pp Hsp); rewrite !allP /"_.[_<-_]" /=.
         rewrite ifF; smt(size_take).
       case (i{hr} < size pp) => Hspp.
       + move : Hbb (H2 pp); rewrite /"_.[_<-_]" /=.
         rewrite ifF; smt(size_take).
       (* bb is at level i{hr} *)
       case (take i{hr} p{m} = take i{hr} pp) => *; last first.
       + (* other path *)
         have ?: bb \in _oram.`bucket (take i{hr} pp) by smt(take_oversize size_take).
         move : (Hps pp _ i{hr} _);smt().
       (* this path *)
       have ? : bb \in stayhere by smt(take_oversize size_take).
       case (bb \in pushed{hr}) => Hip.
       + move => *. move : (H3 bb); rewrite Hip /= => [#] ??Hex.
         elim Hex => ii *; exists ii.
         +  have ? : (take ii p{m}) = (take ii pp); last by smt().
            apply (eq_from_nth witness);smt(size_take nth_take).
        have ? : bb \in _oram.`bucket (take i{hr} pp) by smt(take_size).
           have := block_props _C _oram bb (take i{hr} pp) _; last by smt().
           + rewrite /is_oram.
             move => *; do split; 1:smt().
             move => *; do split. assumption.
             move => *; do split; 1:smt().
             move => *; do split; 1:smt().
             move => *; do split =>/=; 1: by apply Hbase.
             move => *; do split; 1:smt().
             move => *; do split; 1:smt().
             smt().
       (* it remains to prove not in newpushed *)
       have := Hsep bb pp _ _;1,2: smt().
       have := find_rng_out newpushed (fun (b : block) => b.`1 = bb.`1) .
       rewrite hasP => /=;smt().

     + by smt(size_take).

     + move => bb; case (i{hr} = oram{hr}.`height) =>*;1: by smt().
       + rewrite /newpushed ifF 1:/# /=;split.
       + move => H';do split;1:smt().
         + rewrite mem_filter /= in H';smt().
         case (bb \in pushed{hr}); by smt(size_take).
       + move => ? Ht ii *;rewrite mem_filter mem_cat /=;split;1:smt().
         case (bb \in pushed{hr}); 1: smt().
         rewrite H3 /=.
         have -> /= : i{hr} <= _oram.`height by smt().
         have -> /= : take i{hr} bb.`2 = take i{hr} p{m}; last by smt(size_take).
         + move : Ht;rewrite !(take_nth witness); first last;1,3:smt().
         rewrite -!cats1 eqseq_cat; last by smt().
         smt(size_take).

     + rewrite /newpushed /"_.[_]" /=.
       case (i{hr} = oram{hr}.`height) => ?; 1:smt().
       have /= HH := (filter_inj
          (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m}))
          (fun (b : block) => b.`1)
          (fun (block : block) => take (i{hr} + 1) block.`2 = take (i{hr} + 1) p{m})).
       have ? : (forall (i1 i2 : int),
        0 <= i1 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) =>
        0 <= i2 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) =>
        (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) i1).`1 =
        (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{m})) i2).`1 =>
        i1 = i2) ; last by smt().
       move => i1 i2 ??.
       + rewrite /"_.[_]" !nth_cat.
         case (i1 < size pushed{hr}); case (i2 < size pushed{hr}) => ??;1,4:smt(size_cat size_filter List.size_ge0).
         + move => ?; pose b1 := nth witness pushed{hr} i1.
           pose b2 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (i2 - size pushed{hr}).
           have Hb1 : b1 \in pushed{hr} by smt(mem_nth).
           have Hb2 : b2 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
           move : (H3 b1);rewrite Hb1 /= => [#?? Hex];elim Hex => i1' *.
           by smt(size_take).

         + move => ?; pose b2 := nth witness pushed{hr} i2.
           pose b1 := nth witness (oram{hr}.`bucket (take i{hr} p{m})) (i1 - size pushed{hr}).
           have Hb2 : b2 \in pushed{hr} by smt(mem_nth).
           have Hb1 : b1 \in (oram{hr}.`bucket (take i{hr} p{m})) by smt(size_filter size_cat List.size_ge0 mem_nth).
           move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
           by smt(size_take).

     + by assumption.
     + move => Hpre.
       have ^? -> /=: (0 < i{hr} + 1) by smt().
       case: (i{hr} <= size oram{m}.`bpath) => ?.
       + rewrite /"_.[_<-_]" /prefixes.
         rewrite -!map_comp /(\o).
         have ^Hi <-: i{hr} = size (take i{hr} oram{m}.`bpath) by smt(size_take).
         rewrite (range_cat i{hr}); 1,2: by smt().
         rewrite !rangeS !map_cat flatten_cat map1 flatten_seq1 //=.
         have<- //=: take i{hr} p{m} = take i{hr} (take i{hr} oram{m}.`bpath) by smt(take_take).
         rewrite count_cat.
         have->:
            (map
                (fun (x : int) =>
                    if take i{hr} p{m} = take x (take i{hr} oram{m}.`bpath) then
                        stayhere
                    else oram{hr}.`bucket (take x (take i{hr} oram{m}.`bpath)))
                (range 0 i{hr}))
          = (map oram{hr}.`bucket
                (if 0 < i{hr} then prefixes (take (i{hr} - 1) oram{m}.`bpath) else [])).
         + rewrite /prefixes.
           case: (0 < i{hr}) => ?.
           + have<-: i{hr} = size (take (i{hr} - 1) oram{m}.`bpath) + 1 by smt(size_take).
             rewrite -map_comp /(\o).
             apply eq_in_map => x.
             rewrite mem_range => ? //=.
             have -> //=: !take i{hr} p{m} = take x (take i{hr} oram{m}.`bpath) by smt(size_take).
             by smt(take_take).
           + by smt(range_geq).
         have->:
           count
                (fun (b0 : block) =>
                    isprefix (oram{m}.`bpath ++ [p{m}.[size oram{m}.`bpath]]) b0.`2) stayhere = 0.
         + rewrite /stayhere.
           have-> //=: !i{hr} = oram{hr}.`height by smt().
           rewrite count_filter /predI.
           apply count_eq0.
           apply hasPn => x ? //=.
           apply negP => [#] *.
           apply (contra_common_prefix (oram{m}.`bpath ++ [p{m}.[size oram{m}.`bpath]]) x.`2 p{m} (i{hr} + 1)).
           + by assumption.
           + by smt(size_cat size1).
           + by assumption.
           + apply app_isprefix => /#.
         + by exact H_loop_inv2.

       (* case that i{hr} > size oram{m}.`bpath *)
       + rewrite /"_.[_<-_]" /prefixes.
         rewrite -map_comp /(\o).
         have->:
            (map
                (fun (x : int) =>
                    if take i{hr} p{m} = take x (take i{hr} oram{m}.`bpath) then
                        stayhere
                    else oram{hr}.`bucket (take x (take i{hr} oram{m}.`bpath)))
                (range 0 (size (take i{hr} oram{m}.`bpath) + 1))) =
            (map
                (fun (x : int) => oram{hr}.`bucket (take x (take i{hr} oram{m}.`bpath)))
                (range 0 (size (take i{hr} oram{m}.`bpath) + 1))).
         + apply eq_in_map => x.
           rewrite mem_range => /> ? ?.
           by have-> //: !take i{hr} p{m} = take x (take i{hr} oram{m}.`bpath) by smt(size_take).
         have->:
             (map
                (fun (x : int) => oram{hr}.`bucket (take x (take i{hr} oram{m}.`bpath)))
                (range 0 (size (take i{hr} oram{m}.`bpath) + 1)))
           = (map oram{hr}.`bucket
                (if 0 < i{hr} then
                    prefixes (take (i{hr} - 1) oram{m}.`bpath)
                else [])).
         + have-> /=: 0 < i{hr} by smt().
           rewrite /prefixes -map_comp /(\o).
           by rewrite (_: take i{hr} oram{m}.`bpath = take (i{hr} - 1) oram{m}.`bpath); 1: by smt(take_oversize).
         by exact H_loop_inv2.

     + by smt().
   + skip => |> &m1 &m2 Hrel.
     elim Hrel => |> ??? Hcount.
     split.
     (* reachability *)
     + do! split; smt(cats0 List.size_ge0).
     (* inv => post *)
     + move => |> i_L oram_L pushed_L *; do! split; 1: by smt().
       move => ????????????? H_loop_inv1 H_loop_inv2 *.
       have Hpushed_L: pushed_L = [] by smt(mem_eq0).
       split; 1: by smt().
       split; 1: by smt().
       have ?: (predI _C (fun (cc : cell) => size pushed_L <= find (fun (b0 : block) => b0.`1 = cc) pushed_L) = _C).
       + rewrite /predI &(fun_ext) /(==) //= => x.
         rewrite Hpushed_L.
         by smt(size_eq0 find_size).
       + rewrite (_: take (i_L - 1) _ioram.`bpath = _ioram.`bpath) in H_loop_inv2.
         + by smt(take_oversize).
         rewrite (_: 0 < i_L) /= in H_loop_inv2; 1: by smt().
         by assumption.
   if{2}.
   (* flush through the specified path *)
   + wp => //= |>.
     auto => |> //= &m1 &m2 ? H1 H2 H3.
     have H4: isprefix oram{m2}.`bpath p{m2} by done.
     apply H2 in H3.
     rewrite /internal_rel; do! split; 1,2,3,5,6: by smt().
     (* is oram *)
     + move: H1 => />.
     + move => //= b.
       elim H1 => /> 11? Hcount.
       case (b = p{m2}.[size oram{m2}.`bpath]) => Hb.
       + rewrite {2}Hb => @/"_.[_<-_]" //=.
         apply lez_eqVlt; left.
         by rewrite Hb &(H3).
       + rewrite /"_.[_<-_]" //=.
         move: Hcount => /> Hcount.
         have-> //=: !(p{m2}.[size oram{m2}.`bpath] = b) by smt().
         by exact Hcount.
   (* flush outside the specified subtree *)
   + skip => //= |>.
   qed.

   lemma internal_putback (_C : cell -> bool) (_h : int) (_oram : oram) (_ioram : ioram) (b : block):
     equiv[
       ORAM.putback ~ InternalORAM.putback :
          arg{1} = (_oram, b)
       /\ arg{2} = (_ioram, b.`2)
       /\ !_C b.`1
       /\ _oram.`positions b.`1 = b.`2
       /\ internal_rel _C _h _oram _ioram
       ==>
          internal_rel (predU _C (pred1 b.`1)) _h res{1} res{2}
   ].
   proof.
   proc => /=.
   auto => @/internal_rel @/is_ioram |> => 7? Hcount; split => *.
   (* the case that the path of the putback block is in the subtree of bpath *)
   - split; [| split].
     - by smt(is_oram_is_oram_putback).
     - (* is_ioram *)
       by smt().
     - (* counter inequality *)
       move => b0 @/"_.[_<-_]" @/predT //=.
       apply (ler_trans
         (count (fun (b1 : block) => isprefix (_ioram.`bpath ++ [b0]) b1.`2)
            (flatten
                (map
                    _oram.`bucket
                    (prefixes _ioram.`bpath)))
       + (count (fun (b1 : block) => isprefix (_ioram.`bpath ++ [b0]) b1.`2)
            (flatten
                (map
                    (fun (path : path) => if path = [] then [b] else [])
                    (prefixes _ioram.`bpath))))
       )).
       + rewrite !count_flatten -!map_comp !sumzE !BIA.big_mapT /(\o) //=.
         rewrite -BIA.big_split // ler_sum_seq => /> a *.
         case: ([] = take a _ioram.`bpath).
         + move => /> Hcase.
           rewrite count_cat -Hcase //=.
         + by smt().
       apply (ler_trans
         ((_ioram.`counters b0) + (b2i (b.`2.[size _ioram.`bpath] = b0)))
       ); last by smt().
       (* from here, we are going to show that a <= x /\ b <= y so that a + b <= x + y *)
       have: (count
               (fun (b1 : block) => isprefix (_ioram.`bpath ++ [b0]) b1.`2)
               (flatten (map _oram.`bucket (prefixes _ioram.`bpath))))
          <= (_ioram.`counters b0).
       + apply (ler_trans
            (count
                (fun (b1 : block) =>
                    isprefix (_ioram.`bpath ++ [b0]) b1.`2)
                (flatten (map _oram.`bucket (prefixes _ioram.`bpath))))
         ).
         + rewrite ler_eqVlt; left.
           apply count_eq_elem => />.
         by exact Hcount.
       have: (count
                 (fun (b1 : block) => isprefix (_ioram.`bpath ++ [b0]) b1.`2)
                 (flatten
                   (map (fun (path : path) => if path = [] then [b] else [])
                     (prefixes _ioram.`bpath))))
                <= (b2i (b.`2.[size _ioram.`bpath] = b0)).
       + rewrite /prefixes -!map_comp /(\o).
         rewrite range_ltn; 1: by smt(List.size_ge0).
         rewrite map_cons => /> //=.
         rewrite take0 => /> //=.
         rewrite flatten_cons.
         have->: (flatten
                   (map (fun (x : int) => if take x _ioram.`bpath = [] then [b] else [])
                     (range 1 (size _ioram.`bpath + 1)))) = [].
         + apply flatten_map_nil.
           + by smt(mem_range size_take).
         + rewrite cats0 count_seq1 //= &(le_b2i) eq_sym => *.
           have ?: b0 = nth witness (_ioram.`bpath ++ [b0]) (size _ioram.`bpath) by rewrite nth_cat //=.
           have ?: b.`2.[size _ioram.`bpath] = (take (size (_ioram.`bpath ++ [b0])) b.`2).[size _ioram.`bpath] by smt(size_cat nth_take size1).
           by smt().
        by smt().
   (* the case that the path of the putback block is NOT in the subtree of bpath *)
   - split.
     - smt(is_oram_is_oram_putback).
       (* is_ioram has been trivally solved *)
     - (* counter inequality *)
       move => b0 @/predT @/"_.[_<-_]" /> //=.
       apply
         (ler_trans
            (count (fun (b1 : block) => isprefix (_ioram.`bpath ++ [b0]) b1.`2)
               (flatten (map _oram.`bucket (prefixes _ioram.`bpath))))).
       - rewrite !count_flatten -!map_comp !sumzE !BIA.big_mapT /(\o) /=.
         apply ler_sum_seq => i /mem_range rgi _ /=.
         case _: ([] = _) => //= eq.
         - rewrite count_cat /= (_ : b2i _ = 0) //=.
           - apply b2i_eq0.
             have ?: !isprefix _ioram.`bpath b.`2 by done.
             by smt(isprefix_catL).
           rewrite {2} eq ler_eqVlt; left.
           apply count_eq_elem => /#.
         - by exact Hcount.
   qed.

   lemma internal_compile (_h : int) (_oram : oram) (_ioram : ioram) (_p : prog) :
        equiv[ORAM.compile ~ InternalORAM.compile :
                   arg{1} = (_oram, _p)
                /\ arg{2} = (_ioram, _p)
                /\ internal_rel pred0 _h _oram _ioram
                /\ !ORAM.overflow{1} _ioram.`bpath
            ==> ORAM.overflow{1} _ioram.`bpath
                  => res.`ioverflow{2} false \/ res.`ioverflow{2} true].
   proof.
   proc => //=.
   sp.
   pose bp := _ioram.`bpath.
   while (={i, p}
      /\ (0 <= i{1} <= size p{1})
      /\ (exists C, internal_rel C _h o{1} o{2})
      (* all blocks at n can pass the filter *)
      (* main loop invariant *)
      /\ (ORAM.overflow{1} bp
            => o{2}.`ioverflow false \/ o{2}.`ioverflow true)
   ).
   admitted.
   (*
     In the inductive proof, I'm going to prove that:
         ORAM.overflow n
      => K <= |node n|                       (step 1)
      => K <= |filter prefix n|              (step 2)
      => K <= |counter true + counter false| (step 3)
      => exists b, K / 2 <= counter b        (step 4)
      => InternalORAM.overflow               (step 5)

      => exists b, K / 2 <= |prefix n b|   (step 3)
      => exists b, K / 2 <= counter b      (step 4, loop invariant, preserved by single-step lemma)
      => InternalORAM.overflow             (step 5)
   *)
   (* + wp. *)
   (*   match{1}. *)
   (*   (* case: Rd c *) *)
   (*   + inline{1} 1; inline{2} 1. *)
   (*     wp; sp => //=. *)
   (*     elim* => C. *)

   (*     seq 1 1: ( *)
   (*         ={i, p} *)
   (*      /\ c0{1} = c{1} *)
   (*      /\ (0 <= i{1} < size p{1}) *)
   (*      /\ (internal_rel (predI C (predC1 c{1})) _h oram{1} oram{2}) *)
   (*     ecall (internal_fetch C _h oram{1} oram{2} c{1}). *)
   (*     + auto => /> &1 &2 * /#. *)

   (*     seq 1 1: ( *)
   (*         ={i, p} *)
   (*      /\ c0{1} = c{1} *)
   (*      /\ pos{1} = p0{2} *)
   (*      /\ size p0{2} = _h *)
   (*      /\ (0 <= i{1} < size p{1}) *)
   (*      /\ (internal_rel (predI C (predC1 c{1})) _h oram{1} oram{2}) *)
   (*     auto => />; by smt(supp_dlist_size). *)

   (*     sp 1 0. *)
   (*     seq 1 1: ( *)
   (*         ={i, p} *)
   (*      /\ c0{1} = c{1} *)
   (*      /\ pos{1} = p0{2} *)
   (*      /\ (0 <= i{1} < size p{1}) *)
   (*      /\ (internal_rel (predU C (pred1 c{1})) _h oram{1} oram{2}) *)
   (*     ecall (internal_putback (predI C (predC1 c{1})) _h oram{1} oram{2} (c{1}, pos{1}, block{1}.`3)). *)
   (*     + auto => /> &1 &2 *; do! split. *)
   (*       + move => *; do! split. *)
   (*         + by smt(). *)
   (*         + move => *; do! split. *)
   (*           + by move => @/predC1 @/"_.[_<-_]" /#. *)
   (*           + by move => * /#. *)
   (*         + by assumption. *)
   (*         + move => *; do! split. *)
   (*           + move => *; do! split. *)
   (*             + by smt(). *)
   (*             + by move => * /#. *)
   (*             + by assumption. *)

   (*     ecall (internal_flush (predU C (pred1 c{1})) _h oram{1} oram{2}). *)
   (*     + by auto => |> &1 &2 * /#. *)

   (*   (* case: Wt c *) *)
   (*   + inline{1} 1; inline{2} 1. *)
   (*     wp; sp => //=. *)
   (*     elim* => C. *)

   (*     seq 1 1: ( *)
   (*         ={i, p} *)
   (*      /\ (0 <= i{1} < size p{1}) *)
   (*      /\ (internal_rel (predI C (predC1 c{1})) _h oram{1} oram{2}) *)
   (*     ecall (internal_fetch C _h oram{1} oram{2} c{1}). *)
   (*     + by auto => /> &1 &2 * /#. *)

   (*     seq 1 1: ( *)
   (*         ={i, p} *)
   (*      /\ pos{1} = p0{2} *)
   (*      /\ size p0{2} = _h *)
   (*      /\ (0 <= i{1} < size p{1}) *)
   (*      /\ (internal_rel (predI C (predC1 c{1})) _h oram{1} oram{2}) *)
   (*     + by auto => />; by smt(supp_dlist_size). *)

   (*     sp 1 0. *)
   (*     seq 1 1: ( *)
   (*         ={i, p} *)
   (*      /\ pos{1} = p0{2} *)
   (*      /\ (0 <= i{1} < size p{1}) *)
   (*      /\ (internal_rel (predU C (pred1 c{1})) _h oram{1} oram{2}) *)
   (*     ecall (internal_putback (predI C (predC1 c{1})) _h oram{1} oram{2} (c{1}, pos{1}, v0{1})). *)
   (*     + auto => /> &1 &2 *; do! split. *)
   (*       + move => *; do! split. *)
   (*         + by smt(). *)
   (*         + move => *; do! split. *)
   (*           + by move => @/predC1 @/"_.[_<-_]" * /#. *)
   (*           + by move => * /#. *)
   (*         + by assumption. *)
   (*         + move => *; do! split. *)
   (*           + move => *; do! split. *)
   (*             + by smt(). *)
   (*             + by move => * /#. *)
   (*             + by assumption. *)

   (*     ecall (internal_flush (predU C (pred1 c{1})) _h oram{1} oram{2}). *)
   (*     + by auto => |> &1 &2 * /#. *)

   (* + auto => |> *; split. *)
   (*   (* pre => inv *) *)
   (*   + split. *)
   (*     + by exact List.size_ge0. *)
   (*     + by exists pred0; assumption. *)
   (*   (* inv => post *) *)
   (*   + move => * /#. *)
   (* qed. *)

   type loram = {
     lheight   : int;
     counter   : int;
     lpath     : path;
     loverflow : bool;
   }.

   op is_loram (oram : loram) =
        0 < oram.`lheight
     && 0 <= oram.`counter
     && size oram.`lpath = oram.`lheight.

   module LeafORAM = {
     proc fetch(oram : loram) : loram = {
       return oram;
     }

     proc flush(oram : loram) : loram = {
       return oram;
     }

     proc putback(oram : loram, p : path) : loram = {
       if (oram.`lpath = p) {
         oram <- {| oram with
           counter = oram.`counter + 1;
           loverflow = K <= oram.`counter + 1;
         |};
       }

       return oram;
     }

     proc oreadwrite(oram : loram) : loram  = {
       var p : path;
       oram <@ fetch(oram);
       p <$ dlist {0,1} oram.`lheight;
       oram <@ putback(oram, p);
       oram <@ flush(oram);
       return oram;
     }

     proc compile(o : loram, p : prog) : loram = {
       var i : int;
       var v : value;
       i <- 0;
       while (i < size p) {
         o <@ oreadwrite(o);
         i <- i + 1;
       }
       return o;
     }
  }.

  op leaf_rel (C : cell -> bool) (h : int) (oram : oram) (loram : loram) =
       oram.`height = h
    /\ loram.`lheight = h
    /\ is_oram C oram
    /\ is_loram loram
    /\ (let bcks : block list list = map (fun p => oram.`bucket p) (prefixes loram.`lpath) in
            count (fun v : _ * _ * _ => v.`2 = loram.`lpath) (flatten bcks)
         <= loram.`counter).

  op leaf_rel_fetch (C: cell -> bool) (h : int) (c : cell) (oram : oram) (loram : loram) =
        oram.`height = h
     /\ loram.`lheight = h
     /\ is_oram_fetch C c oram
     /\ is_loram loram
    /\ (let bcks : block list list = map (fun p => oram.`bucket p) (prefixes loram.`lpath) in
            count (fun v : _ * _ * _ => v.`2 = loram.`lpath) (flatten bcks)
         <= loram.`counter).

  lemma leaf_rel_is_oram (loram : loram) (C : cell -> bool) (h : int) (oram : oram) :
    leaf_rel C h oram loram => is_oram C oram.
  proof. by move=> @/leaf_rel. qed.

  lemma leaf_rel_is_loram (C : cell -> bool) (h : int) (oram : oram) (loram : loram) :
    leaf_rel C h oram loram => is_loram loram.
  proof. by move=> @/leaf_rel. qed.

  lemma leaf_rel_eq_height (C : cell -> bool) (h : int) (oram : oram) (loram : loram) :
    leaf_rel C h oram loram => oram.`height = loram.`lheight.
  proof. by smt(). qed.
  
  lemma is_oram_pred0_leaf_rel (h : int) (oram : oram) (loram : loram) :
    is_oram pred0 oram => leaf_rel pred0 h oram loram.
  admitted.

  lemma leaf_fetch (C: cell -> bool) (h : int) (o : oram) (lo : loram) (c0 : cell) :
    equiv[ORAM.fetch ~ LeafORAM.fetch :
       arg{1} = (o, c0) /\ arg{2} = lo /\ leaf_rel C h o lo
    ==>
       leaf_rel (predI C (predC1 c0)) h res{1}.`1 res{2}
    ].
  proof.
  proc => /=; sp.
  while{1} (0 <= i{1} <= oram{1}.`height + 1
     /\ pos{1} = oram{1}.`positions c{1}
     /\ c{1} = c0
     /\ leaf_rel_fetch C h c0 oram{1} oram{2}
     /\ (forall _p _i, 0 <= _i < i{1} =>
                        size _p = oram{1}.`height =>
            let block = oram{1}.`bucket (take _i _p) in
              !(has (fun (block : block) => block.`1 = c0) block)))
    (oram{1}.`height - i{1} + 1).
  (* inv => inv *)
  + auto => /> &hr 7? He 5? H_count *; do split.
    + move => *; do split; 1,2,6: smt().
      (* is oram *)
      + move => *;split;1: by smt(mem_trim).
        move => *;split;1: by smt(mem_trim).
        move => *;split.
        + move => _c0 *.
          elim (He _c0 _); 1:smt().
          move => //= ip [Hip Heip]; exists ip; split; 1:smt().
          move => Hipp /=; rewrite hasP in Heip; elim Heip => /= b' Hb.
          rewrite hasP => /=; exists b';split;2:smt().
          by smt(trim_mem).
          by smt(mem_trim find_trim_lt find_trim_ge size_trim trim_id).
      + apply
          (ler_trans
            (count (fun (v0 : cell * path * value) => v0.`2 = oram{m}.`lpath)
              (flatten (map oram{hr}.`bucket (prefixes oram{m}.`lpath))))).
        move => /> @/prefixes @/"_.[_<-_]".
        rewrite -!map_comp /(\o).
        rewrite (range_cat i{hr}); 1,2: smt().
        rewrite (range_cat (i{hr} + 1) i{hr}); 1,2: smt().
        rewrite !map_cat !flatten_cat !count_cat.
        rewrite (_:
            (map
                (fun (x : int) =>
                oram{hr}.`bucket.[take i{hr} (oram{hr}.`positions c0) <-
                    trim (oram{hr}.`bucket (take i{hr} (oram{hr}.`positions c0)))
                    (find (fun (x0 : block) => x0.`1 = c0) (oram{hr}.`bucket
                        (take i{hr} (oram{hr}.`positions c0))))]
                (take x oram{m}.`lpath)) (range 0 i{hr}))
          = (map
                (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`lpath))
                (range 0 i{hr}))).
        + apply eq_in_map => x.
          rewrite mem_range => ? //=.
          have ? //=: !take i{hr} (oram{hr}.`positions c0) = take x oram{m}.`lpath by smt(size_take).
          by smt().
        rewrite (_:
            (map
                (fun (x : int) =>
                    oram{hr}.`bucket.[take i{hr} (oram{hr}.`positions c0) <-
                    trim (oram{hr}.`bucket (take i{hr} (oram{hr}.`positions c0)))
                        (find (fun (x0 : block) => x0.`1 = c0) (oram{hr}.`bucket
                        (take i{hr} (oram{hr}.`positions c0))))]
                    (take x oram{m}.`lpath))
                (range (i{hr} + 1) (size oram{m}.`lpath + 1)))
          = (map
                (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`lpath))
                (range (i{hr} + 1) (size oram{m}.`lpath + 1)))).
        + apply eq_in_map => x.
          rewrite mem_range => ? //=.
          have ? //=: !take i{hr} (oram{hr}.`positions c0) = take x oram{m}.`lpath by smt(size_take).
          by smt().
        rewrite !rangeS !map1 !flatten1 //=.
        apply lez_add2l.
        apply lez_add2r.
        apply count_subseq.
        + by case _ : (_ = _) => //=; smt(subseq_trim).
        by assumption.
     (* exactly same as before *)
     + move => pp ii???.
       case (ii = i{hr}); 2: by smt(size_take).
       move => Hii1; rewrite Hii1 /=.
       case (take i{hr} (oram{hr}.`positions c0) = take i{hr} pp).
       + by move => -> /=; rewrite /"_.[_<-_]" /=; apply mem_uniq_triple; apply uniq_cells => /#.
       move => Hpp; rewrite  /"_.[_<-_]" Hpp /=; rewrite hasP negb_exists /= /#.

    (* similar as before *)
    + move => *; do! split; 1,2,4: smt().
      move => pp ii *.
      case (ii = i{hr}); 2: by smt(size_take).
      move => Hii1; rewrite Hii1 /=.
      case (take i{hr} (oram{hr}.`positions c0) = take i{hr} pp).
      + by move => <-; rewrite has_find //=.
      + move => Hpp; rewrite hasP negb_exists /= /#.

  (* inv => pos *)
  + auto => />.
    move => /> &1 &2 *; do! split; 1..4: by smt().
    + move => i_L oram_L; do! split.
      + move => * /#.
      + move => 12? H_counting_ineq_L Hnc pp ? bb.
        + have := Hnc (pp++nseq (oram_L.`height - size pp) false) (size pp) _ _;1,2: smt(size_cat size_nseq List.size_ge0).
          by rewrite hasPn;smt(take_size_cat).
  qed.

  lemma leaf_flush (C : cell -> bool) (h : int) (o : oram) (lo : loram) :
    equiv[ORAM.flush ~ LeafORAM.flush :
        arg{1} = o /\ arg{2} = lo /\ leaf_rel C h o lo
      ==>
        leaf_rel C h res{1} res{2}
    ].
  proof.
  proc.
  seq 1 0: (
     leaf_rel C h oram{1} oram{2}
  /\ oram{1} = o
  /\ oram{2} = lo
  /\ size p{1} = oram{1}.`height).
  + rnd{1}.
    auto => &1 &2 ? p0.
    by smt(supp_dlist_size).
  sp 2 0.
  while{1} (0 <= i{1} <= oram{1}.`height + 1
     /\ size p{1} = oram{1}.`height
     /\ oram{1}.`height = o.`height
     /\ oram{1}.`positions = o.`positions
     /\ oram{2} = lo
     /\ oram{1}.`height = oram{2}.`lheight
     /\ leaf_rel C h o lo
     /\ leaf_rel (predI C (fun c => size pushed{1} <= find (fun (b : block) => b.`1 = c) pushed{1})) h oram{1} oram{2}
     /\ (let bcks : block list list = map (fun p => oram{1}.`bucket p{1}) (prefixes oram{2}.`lpath) in
            count
               (fun v : _ * _ * _ => v.`2 = oram{2}.`lpath)
               (flatten bcks ++ (if take i{1} p{1} = take i{1} oram{2}.`lpath then pushed{1} else []))
         <= oram{2}.`counter)
     (* block is in pushed iff it was higher up in the path of _oram, agress on the flushing path p, and it's not in the higher path of the current oram *)
     /\ (forall bb, bb \in pushed{1} <=>
             (i{1} <= o.`height
           /\ take i{1} bb.`2 = take i{1} p{1}
           /\ (exists ii, 0 <= ii < i{1} /\ bb \in o.`bucket (take ii p{1}))))
     (* we have no repeats in pushed *)
     /\ (forall i1 i2,
             0 <= i1 < size pushed{1}
           => 0 <= i2 < size pushed{1}
           => pushed{1}.[i1].`1 = pushed{1}.[i2].`1
           => i1 = i2)
     (* Whatever is in current oram first levels is not in pushed and it was somewhere above in the original _oram *)
     /\ (forall _p, size _p < i{1} =>
          (all (fun (block : block) =>
            !block \in pushed{1} /\
             (exists ii, 0<= ii <= size _p /\ block \in o.`bucket (take ii _p))) (oram{1}.`bucket _p)))
     (* Whatever is in current oram later levels is untouched from _oram *)
     /\ (forall _p, i{1} <= size _p <= oram{1}.`height => oram{1}.`bucket _p = o.`bucket _p)
  ) (oram{1}.`height - i{1} + 1).
  (* inv => inv *)
  + auto => @/leaf_rel |> //= &hr 14? H3 H4 H1 H2 *.
    rewrite !case_elim.

    pose newpushed := (if i{hr} = oram{hr}.`height then []
        else
          filter
            (fun (block : block) =>
               take (i{hr} + 1) block.`2 = take (i{hr} + 1) p{hr})
            (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{hr}))).
    pose stayhere := if i{hr} = oram{hr}.`height then
                 pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{hr})
               else
                 filter
                   (fun (block : block) =>
                      take (i{hr} + 1) block.`2 <> take (i{hr} + 1) p{hr})
                   (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{hr})).

     (* setting the ground *)
     have ? : forall b, (!b \in newpushed /\ !b \in stayhere) => !b \in pushed{hr}.
     + case (i{hr} = oram{hr}.`height); 1: by smt(mem_cat).
       by rewrite /newpushed /stayhere => ->b /=; rewrite !mem_filter !mem_cat /#.

     have ? : forall b, b \in stayhere => !b \in pushed{hr} => b \in oram{hr}.`bucket (take i{hr} p{hr}).
     + rewrite /stayhere;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
        by move => b;rewrite !mem_filter !mem_cat /#.

     have H_newpushed_not_pushed : forall b, b \in newpushed => !b \in pushed{hr} => b \in oram{hr}.`bucket (take i{hr} p{hr}).
     + rewrite /newpushed;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
        by move => b;rewrite !mem_filter !mem_cat /#.

     have ? : forall b, b \in stayhere => !b \in newpushed.
     + rewrite /stayhere /newpushed;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
        by move => b;rewrite !mem_filter !mem_cat /#.

     have ? : forall b, !b \in stayhere => !b \in newpushed => !b \in oram{hr}.`bucket (take i{hr} p{hr}).
     + rewrite /stayhere /newpushed;case (i{hr} = oram{hr}.`height) => ?/=;1: by smt(mem_cat).
        by move => b;rewrite !mem_filter !mem_cat /#.

     have ?: forall bb1 bb2, bb1 \in stayhere => bb2 \in newpushed => bb1.`2 <> bb2.`2.
     + rewrite /stayhere /newpushed => bb1 bb2.
       case (i{hr} = oram{hr}.`height) => ? //.
       by rewrite !mem_filter //= /#.

     have Hsep : forall bb pp, size pp <= oram{hr}.`height =>
         bb \in oram{hr}.`bucket.[take i{hr} p{hr} <- stayhere] pp =>
             size newpushed <= find (fun (b : block) => b.`1 = bb.`1) newpushed.
    + have: is_oram C o by assumption.
      rewrite /is_oram => /> 5? Hinjb ?.
      move => bb pp ??;
       have [ _ Hin]  := find_rng_in newpushed (fun (b : block) => b.`1 = bb.`1).
       rewrite implybE in Hin;elim Hin;1: by smt(find_ge0).
       rewrite hasP=> Hex;elim Hex => b2 /= *.
       case (b2 \in stayhere) => *; 1: by smt().
       case (i{hr} < size pp) => *.  (* block is below *)
        + have ? : bb \in o.`bucket pp by smt(size_take).
          pose i1 := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket pp).
          have i1b := find_rng_in (o.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
          case (b2 \in pushed{hr}) => Hb2.
            + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i2' p{hr})).
              have := Hinjb (take i2' p{hr}) pp i2f i1 _ _ _;2,4:smt(size_take nth_find mem_nth).
              + have := (find_rng_in (o.`bucket (take i2' p{hr})) (fun (bf : block) => bf.`1 = b2.`1));1: by rewrite hasP; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i2' p{hr})) _;1: by rewrite ?
hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _;rewrite ?
hasP /=; smt().
          have ? : b2 \in o.`bucket (take i{hr} p{hr}) by smt(size_take).
          pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i{hr} p{hr})).
          have := Hinjb (take i{hr} p{hr}) pp i2f i1 _ _ _;2,4:smt().
              + have :=  find_rng_in (o.`bucket (take i{hr} p{hr})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
              have /= :=  nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i{hr} p{hr})) _;1: by rewrite hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _; by rewrite ?hasP /=; smt().
        case (size pp < i{hr}) => *.
        (* block is above *)
        + have ? : pp <> take i{hr} p{hr} by smt(size_take).
          move : (H1 pp _); 1: by smt().
          rewrite allP => /> Hbs; move : (Hbs bb _);1:smt().
          move =>  [#? Hex];elim Hex => i1' *.
          have ? : bb \in o.`bucket (take i1' pp) by smt().
          pose i1f := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket (take i1' pp)).
          case (b2 \in pushed{hr}) => Hb2.
            + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i2' p{hr})).
              have := Hinjb (take i2' p{hr}) (take i1' pp) i2f i1f _ _ _; 4:  by smt().
              + have := find_rng_in (o.`bucket (take i2' p{hr})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
              + have := find_rng_in (o.`bucket (take i1' pp)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i2' p{hr})) _.
              + rewrite ?hasP /=.
                exists b2.
                by smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket (take i1' pp)) _.
              + rewrite ?hasP.
                exists bb.
                by smt().
              by smt().

          have ? : b2 \in o.`bucket (take i{hr} p{hr}) by smt(size_take).
          pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i{hr} p{hr})).
          have := Hinjb (take i{hr} p{hr}) (take i1' pp) i2f i1f _ _ _;4:smt(size_take).
          + have := find_rng_in (o.`bucket (take i{hr} p{hr})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
          + have := find_rng_in (o.`bucket (take i1' pp)) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
          have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i{hr} p{hr})) _;1: by rewrite ?hasP;smt(nth_find).
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket (take i1' pp)) _; by rewrite ?hasP /=; smt().

        + (* block is at this level *)
          case (pp = take i{hr} p{hr}) => *; last first.
          + have Hinn : bb \in o.`bucket pp by smt().
          pose i1 := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket pp).
          have i1b := find_rng_in (o.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
          case (b2 \in pushed{hr}) => Hb2.
            + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
              pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i2' p{hr})).
              have := Hinjb (take i2' p{hr}) pp i2f i1 _ _ _;2,4:smt(size_take).
              + have := find_rng_in (o.`bucket (take i2' p{hr})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i2' p{hr})) _;1: by rewrite ?hasP;smt(nth_find).
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _; by rewrite ?hasP /=; smt().

            have ? : b2 \in o.`bucket (take i{hr} p{hr}) by smt(size_take).
            pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i{hr} p{hr})).
            have := Hinjb (take i{hr} p{hr}) pp i2f i1 _ _ _;2,4:smt(size_take).
            + have := find_rng_in (o.`bucket (take i{hr} p{hr})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
            have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i{hr} p{hr})) _;1: by rewrite ?hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _; by rewrite ?hasP /=; smt().

        + have ? : bb \in stayhere;1: by smt().
          case (bb \in pushed{hr}) => Hpps;last first.
          +  have ? : bb \in (o.`bucket pp) by smt().
             pose i1 := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket pp).
             have i1b := find_rng_in (o.`bucket pp) (fun (bf : block) => bf.`1 = bb.`1); rewrite hasP in i1b.
             case (b2 \in pushed{hr}) => Hb2.
              + move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
                pose i2f := find (fun (b : block) => b.`1 = b2.`1) (o.`bucket (take i2' p{hr})).
                have := Hinjb (take i2' p{hr}) pp i2f i1 _ _ _;2,4:smt().
                + have := find_rng_in (o.`bucket (take i2' p{hr})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
                have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i2' p{hr})) _;1: by rewrite ?hasP /=; smt().
              have /= := nth_find witness  (fun (bf : block) => bf.`1 = bb.`1) (o.`bucket pp) _; by rewrite ?hasP /=; smt().

             have ? : b2 \in o.`bucket (take i{hr} p{hr}) by smt().
             pose i2f := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket (take i{hr} p{hr})).
             have := Hinjb (take i{hr} p{hr}) pp i2f i1 _ _ _;2,4:smt().
             + have := find_rng_in (o.`bucket (take i{hr} p{hr})) (fun (bf : block) => bf.`1 = b2.`1);1: by rewrite hasP; smt().
             have /= := nth_find witness  (fun (bf : block) => bf.`1 = b2.`1) (o.`bucket (take i{hr} p{hr})) _; by rewrite ?hasP /=; smt().

             case (b2 \in pushed{hr}) => Hb2.
              + pose i1f := find (pred1 bb) pushed{hr}.
                pose i2f := find (pred1 b2) pushed{hr}.
                move : (H4 i1f i2f); smt().

             move : (H3 bb);rewrite Hpps /= => [#?? Hex];elim Hex => i1' *.
             pose i1f := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket (take i1' p{hr})).
             have ? : b2 \in o.`bucket (take i{hr} p{hr}) by smt().
             pose i2f := find (fun (b : block) => b.`1 = bb.`1) (o.`bucket (take i{hr} p{hr})).
             have := Hinjb (take i{hr} p{hr}) (take i1' p{hr}) i2f i1f _ _ _;3..:smt().
             + have := find_rng_in (o.`bucket (take i{hr} p{hr})) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().
             + have := find_rng_in (o.`bucket (take i1' p{hr})) (fun (bf : block) => bf.`1 = bb.`1);1: by rewrite hasP; smt().

      (* pushed{hr} + bucket (take i{hr} p{hr}) = stayhere + newpushed *)
      have ?: forall b, (b \in pushed{hr} \/ b \in (oram{hr}.`bucket (take i{hr} p{hr}))) <=> (b \in stayhere \/ b \in newpushed).
      + smt().

      (* pushed{hr} /\ bucket (take i{hr} p{hr}) = \emptyset *)
      (* have ?: forall b, (b \in pushed{hr}) => !b \in (oram{hr}.`bucket (take i{hr} p{hr})). *)
      (* + smt(). *)

      (* stayhere /\ newpushed = \emptyset *)
      have ?: forall b, (b \in stayhere) => !(b \in newpushed).
      + smt().

      have ?: perm_eq (pushed{hr} ++ (oram{hr}.`bucket (take i{hr} p{hr}))) (stayhere ++ newpushed).
      + rewrite /stayhere /newpushed.
        case: (i{hr} = oram{hr}.`height) => ?.
        + rewrite cats0 perm_eq_refl //=.
        + rewrite (_:
             (fun (block : block) =>
                 take (i{hr} + 1) block.`2 = take (i{hr} + 1) p{hr})
           = predC
                 (fun (block : block) =>
                     take (i{hr} + 1) block.`2 <> take (i{hr} + 1) p{hr})).
          + rewrite /predC //=.
          rewrite perm_eq_sym perm_filterC.

      have H_map_small:
         (map
             (fun (x : int) =>
             if take i{hr} p{hr} = take x oram{m}.`lpath then stayhere
             else oram{hr}.`bucket (take x oram{m}.`lpath)) (range 0 i{hr}))
       =
         (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`lpath)) (range 0 i{hr})).
      + apply eq_in_map => x />.
        rewrite mem_range => ?.
        have-> //: !take i{hr} p{hr} = take x oram{m}.`lpath.
        smt(size_take).

      have H_map_large:
         (map
             (fun (x : int) =>
                 if take i{hr} p{hr} = take x oram{m}.`lpath then stayhere
                 else oram{hr}.`bucket (take x oram{m}.`lpath))
             (range (i{hr} + 1) (size oram{m}.`lpath + 1)))
         = (map (fun (x : int) => oram{hr}.`bucket (take x oram{m}.`lpath))
             (range (i{hr} + 1) (size oram{m}.`lpath + 1))).
      + apply eq_in_map => x />.
        rewrite mem_range => ?.
        by have-> //: !take i{hr} p{hr} = take x oram{m}.`lpath by smt(size_take).

     have Hcount:
         count (fun (v : cell * path * value) => v.`2 = oram{m}.`lpath)
             (flatten
                 (map oram{hr}.`bucket.[take i{hr} p{hr} <- stayhere]
                 (prefixes oram{m}.`lpath))
              ++ (if take (i{hr} + 1) p{hr} = take (i{hr} + 1) oram{m}.`lpath then newpushed else []))
      <= oram{m}.`counter.
     + apply (ler_trans
                 (count (fun (v : cell * path * value) => v.`2 = oram{m}.`lpath)
                        (flatten (map oram{hr}.`bucket (prefixes oram{m}.`lpath)) ++
                         if take i{hr} p{hr} = take i{hr} oram{m}.`lpath then pushed{hr} else []))
       ); last by assumption.
       + rewrite /"_.[_<-_]" /prefixes.
         rewrite count_cat -!map_comp /(\o).
         rewrite (range_cat i{hr}); 1,2: smt().
         rewrite (range_cat (i{hr} + 1) i{hr}); 1,2: smt().
         rewrite !map_cat !flatten_cat !count_cat.
         rewrite H_map_small H_map_large.
         rewrite !rangeS !map1 !flatten1 //=.
         have:
           count
             (fun (v : cell * path * value) => v.`2 = oram{m}.`lpath)
             (stayhere ++ newpushed)
         = count
             (fun (v : cell * path * value) => v.`2 = oram{m}.`lpath)
             (oram{hr}.`bucket (take i{hr} p{hr}) ++ pushed{hr}).
         + by rewrite &(perm_eqP) perm_eq_sym perm_catCl //=.
         case: (take (i{hr} + 1) p{hr} = take (i{hr} + 1) oram{m}.`lpath) => Htake1.
         + have Htake: take i{hr} p{hr} = take i{hr} oram{m}.`lpath by smt(take_take size_take).
           by rewrite !count_cat /#.
         case: (take i{hr} p{hr} = take i{hr} oram{m}.`lpath) => Htake.
         + have: count
                    (fun (v : cell * path * value) => v.`2 = oram{m}.`lpath)
                    (newpushed)
                  = 0.
           + rewrite /newpushed.
             case: (i{hr} = oram{hr}.`height) => //=.
             rewrite count_filter /predI.
             rewrite (_:
                         (fun (x : cell * path * value) => x.`2 = oram{m}.`lpath /\ take (i{hr} + 1) x.`2 = take (i{hr} + 1) p{hr})
                         = pred0); 1: by smt().
             by rewrite count_pred0 //=.
           by rewrite !count_cat /#.
         + by smt().

     (* extract is_oram by stupid split *)
     split; 2: by smt().
     split; 1: by smt().
     split; 1: split.
     + apply (is_oram_is_oram_flush C oram{hr} o i{hr} p{hr} pushed{hr}) => //= /#.
     + by smt(count_cat count_ge0).
     (* is_oram is proved, let's do crazy split *)
     do! split.
     + by assumption.

     + move => bb; case (i{hr} = oram{hr}.`height) =>*;1: by smt().
       rewrite /newpushed ifF 1:/# /=;split.
       + move => H';do split;1:smt().
         + rewrite mem_filter /= in H';smt().
         case (bb \in pushed{hr}); by smt(size_take).
       + move => ? Ht ii *;rewrite mem_filter mem_cat /=;split;1:smt().
         case (bb \in pushed{hr}); 1: smt().
         rewrite H3 /=.
         have -> /= : i{hr} <= o.`height by smt().
         have -> /= : take i{hr} bb.`2 = take i{hr} p{hr}; last by smt(size_take).
         + move : Ht;rewrite !(take_nth witness); first last;1,3:smt().
         rewrite -!cats1 eqseq_cat; last by smt().
         by smt(size_take).

      + rewrite /newpushed /"_.[_]" /=.
        case (i{hr} = oram{hr}.`height) => ?; 1:smt().
        have /= HH := (filter_inj
           (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{hr}))
           (fun (b : block) => b.`1)
           (fun (block : block) => take (i{hr} + 1) block.`2 = take (i{hr} + 1) p{hr})).
        have ? : (forall (i1 i2 : int),
         0 <= i1 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{hr})) =>
         0 <= i2 < size (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{hr})) =>
         (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{hr})) i1).`1 =
         (nth witness (pushed{hr} ++ oram{hr}.`bucket (take i{hr} p{hr})) i2).`1 =>
         i1 = i2) ; last by smt().
        move => i1 i2 ??.
        + rewrite /"_.[_]" !nth_cat.
          case (i1 < size pushed{hr}); case (i2 < size pushed{hr}) => ??;1,4:smt(size_cat size_filter List.size_ge0).
          + move => ?; pose b1 := nth witness pushed{hr} i1.
            pose b2 := nth witness (oram{hr}.`bucket (take i{hr} p{hr})) (i2 - size pushed{hr}).
            have Hb1 : b1 \in pushed{hr} by smt(mem_nth).
            have Hb2 : b2 \in (oram{hr}.`bucket (take i{hr} p{hr})) by smt(size_filter size_cat List.size_ge0 mem_nth).
            move : (H3 b1);rewrite Hb1 /= => [#?? Hex];elim Hex => i1' *.
            have Hbb2: b2 \in o.`bucket (take i{hr} p{hr}) by smt(size_take).
            have ? : take i1' p{hr} = take i{hr} p{hr}.
            + apply (is_oram_bbpp C o b1 b2 (take i1' p{hr}) (take i{hr} p{hr})) => //= /#.
            by smt(size_take).

          + move => ?; pose b2 := nth witness pushed{hr} i2.
            pose b1 := nth witness (oram{hr}.`bucket (take i{hr} p{hr})) (i1 - size pushed{hr}).
            have Hb2 : b2 \in pushed{hr} by smt(mem_nth).
            have Hb1 : b1 \in (oram{hr}.`bucket (take i{hr} p{hr})) by smt(size_filter size_cat List.size_ge0 mem_nth).
            move : (H3 b2);rewrite Hb2 /= => [#?? Hex];elim Hex => i2' *.
            have Hbb1: b1 \in o.`bucket (take i{hr} p{hr}) by smt(size_take).
            have ? : take i{hr} p{hr} = take i2' p{hr}.
            + apply (is_oram_bbpp C o b1 b2 (take i{hr} p{hr}) (take i2' p{hr})) => //= /#.
            by smt(size_take).

     + have: is_oram C o by assumption.
       move => /> ???? Hbase Hinjb Hps.
       move => pp ?; rewrite allP => bb Hbb /=; split;last first.
       (* basic properties *)
       case (size pp < i{hr}) => Hsp.
       + move : Hbb (H1 pp Hsp); rewrite !allP /"_.[_<-_]" /=.
         rewrite ifF; smt(size_take).
       case (i{hr} < size pp) => Hspp.
       + move : Hbb (H2 pp); rewrite /"_.[_<-_]" /=.
         rewrite ifF; smt(size_take).
       (* bb is at level i{hr} *)
       case (take i{hr} p{hr} = take i{hr} pp) => *; last first.
       + (* other path *)
         have ?: bb \in o.`bucket (take i{hr} pp) by smt(take_oversize size_take).
         move : (Hps pp _ i{hr} _);smt().
       (* this path *)
       have ? : bb \in stayhere by smt(take_oversize size_take).
       case (bb \in pushed{hr}) => Hip.
       + move => *. move : (H3 bb); rewrite Hip /= => [#] ??Hex.
         elim Hex => ii *; exists ii.
         + have ? : (take ii p{hr}) = (take ii pp); last by smt().
           rewrite (_: take ii p{hr} = take ii (take i{hr} p{hr})); 1: smt(take_take).
           rewrite (_: take ii pp = take ii (take i{hr} pp)); 1: smt(take_take).
           by smt().
        have ? : bb \in o.`bucket (take i{hr} pp) by smt(take_size).
           have := block_props C o bb (take i{hr} pp) _; last by smt().
           by assumption.
       (* it remains to prove not in newpushed *)
       have := Hsep bb pp _ _;1,2: smt().
       have := find_rng_out newpushed (fun (b : block) => b.`1 = bb.`1) .
       rewrite hasP => /=;smt().

     + smt(size_take).

  (* pre => inv *)
  + auto => @/leaf_rel |> //= &1 &2 *; do! split; 1,2,4,5: smt().
    + rewrite cats0; by assumption.
    + smt(List.size_ge0).
    (* inv => pos *)
    + move => i_L oram_L pushed_L *; do! split.
      + move => * /#.
      + move => *.
        have Hpushed_L: pushed_L = [] by smt(mem_eq0).
        rewrite -(_:
            (predI C
                (fun (c : cell) => size pushed_L <= find (fun (b : block) => b.`1 = c) pushed_L))
          = C) 1: /#.
        by assumption.
qed.

  lemma leaf_putback (C : cell -> bool) (h : int) (o : oram) (lo : loram) (b : block) :
    equiv[ORAM.putback ~ LeafORAM.putback :
        arg{1} = (o, b)
     /\ arg{2} = (lo, b.`2)
     /\ !C b.`1
     /\ leaf_rel C h o lo
     /\ o.`positions b.`1 = b.`2
    ==>
        leaf_rel (predU C (pred1 b.`1)) h res{1} res{2}
  ].
  proof.
  proc => //=.
  auto => @/leaf_rel @/is_loram |> 7? Hcount; split => *.
  + split; [| split].
    - by smt(is_oram_is_oram_putback).
    - by smt().
    + apply (ler_trans
                 (count
                     (fun (v : cell * path * value) => v.`2 = lo.`lpath)
                     (flatten (map o.`bucket (prefixes lo.`lpath))) + 1)); last by smt().
      rewrite /"_.[_<-_]" /prefixes -!map_comp /(\o).
      rewrite (range_cat 1); 1,2: smt().
      rewrite rangeS !map_cat !flatten_cat !count_cat.
      rewrite (_:
        (map
            (fun (x : int) =>
            if [] = take x lo.`lpath then o.`bucket [] ++ [b]
            else o.`bucket (take x lo.`lpath)) (range 1 (size lo.`lpath + 1)))
      =
        (map (fun (x : int) => o.`bucket (take x lo.`lpath))
            (range 1 (size lo.`lpath + 1)))
      ).
      + by apply eq_in_map => /> x; smt(mem_range).
      rewrite addzC.
      rewrite (addzC
        (count (fun (v : cell * path * value) => v.`2 = lo.`lpath)
          (flatten (map (fun (x : int) => o.`bucket (take x lo.`lpath)) [0])))
        (count (fun (v : cell * path * value) => v.`2 = lo.`lpath)
            (flatten
                (map (fun (x : int) => o.`bucket (take x lo.`lpath))
                    (range 1 (size lo.`lpath + 1)))))).
      rewrite -addzA.
      apply lez_add2l.
      rewrite map1 //= !flatten1 take0 //= !count_cat.
      by smt(count_size).
  + split.
    + by smt(is_oram_is_oram_putback).
    + apply (ler_trans
                 (count
                     (fun (v : cell * path * value) => v.`2 = lo.`lpath)
                     (flatten (map o.`bucket (prefixes lo.`lpath))))); last by smt().
      rewrite /"_.[_<-_]" /prefixes -!map_comp /(\o).
      rewrite (range_cat 1); 1,2: smt().
      rewrite rangeS !map_cat !flatten_cat !count_cat.
      rewrite (_:
        (map
            (fun (x : int) =>
            if [] = take x lo.`lpath then o.`bucket [] ++ [b]
            else o.`bucket (take x lo.`lpath)) (range 1 (size lo.`lpath + 1)))
      =
        (map (fun (x : int) => o.`bucket (take x lo.`lpath))
            (range 1 (size lo.`lpath + 1)))
      ).
      + by smt(eq_in_map mem_range).
      rewrite !map1 //= !flatten1 take0 //= count_cat.
      have: count (fun (v : cell * path * value) => v.`2 = lo.`lpath) [b] = 0.
      + apply count_eq0 => /#.
      by smt().
  qed.

  lemma leaf_compile (_h : int) (_oram : oram) (_loram : loram) (_p : prog) :
       equiv[ORAM.compile ~ LeafORAM.compile :
                  arg{1} = (_oram, _p)
               /\ arg{2} = (_loram, _p)
               /\ leaf_rel pred0 _h _oram _loram
               /\ !(ORAM.overflow{1} _loram.`lpath)
           ==>
              ORAM.overflow{1} _loram.`lpath => res.`loverflow{2}
              (* (let bcks : block list list = map (fun p => res{1}.`1.`bucket p) (prefixes res{2}.`lpath) in *)
              (*       count (fun v : _ * _ * _ => v.`2 = res{2}.`lpath) (flatten bcks) *)
              (*   <= res{2}.`counter) *)
       ].
  proof.
  proc => //=.
  sp.
  while (
       ={i, p}
    /\ (0 <= i{1} <= size p{1})
    /\ (exists C, leaf_rel C _h o{1} o{2})
  ).
  + match{1}.
    (* case: Rd c *)
    + inline{1} 1; inline{2} 1.
      wp; sp => //=.
      elim* => C.

      seq 1 1: (
          ={i, p}
       /\ c0{1} = c{1}
       /\ (0 <= i{1} < size p{1})
       /\ (leaf_rel (predI C (predC1 c{1})) _h oram{1} oram{2})
      ).
      ecall (leaf_fetch C _h oram{1} oram{2} c{1}).
      + by auto => /> &1 &2 * /#.

      seq 1 1: (
          ={i, p}
       /\ c0{1} = c{1}
       /\ pos{1} = p0{2}
       /\ size p0{2} = _h
       /\ (0 <= i{1} < size p{1})
       /\ (leaf_rel (predI C (predC1 c{1})) _h oram{1} oram{2})
      ).
      + by auto => />; by smt(supp_dlist_size).

      sp 1 0.
      seq 1 1: (
          ={i, p}
       /\ c0{1} = c{1}
       /\ pos{1} = p0{2}
       /\ (0 <= i{1} < size p{1})
       /\ (leaf_rel (predU C (pred1 c{1})) _h oram{1} oram{2})
      ).
      ecall (leaf_putback (predI C (predC1 c{1})) _h oram{1} oram{2} (c{1}, pos{1}, block{1}.`3)).
      + auto => /> &1 &2 *; do! split.
        + move => *; do! split.
          + by smt().
          + move => *; do! split.
            + by move => @/predC1 @/"_.[_<-_]" /#.
            + by move => * /#.
          + move => 23? Hfull *; do! split.
            + by smt().
            + move => ? c1.
              have->: (predU C (pred1 c{1})) = (predU (predI C (predC1 c{1})) (pred1 c{1})) by smt().
              by have /# := Hfull c1.

      ecall (leaf_flush (predU C (pred1 c{1})) _h oram{1} oram{2}).
      + by auto => |> &1 &2 * /#.

    (* case: Wt c *)
    + inline{1} 1; inline{2} 1.
      wp; sp => //=.
      elim* => C.

      seq 1 1: (
          ={i, p}
       /\ c{1} = t{1}.`1 /\ v0{1} = t{1}.`2
       /\ (0 <= i{1} < size p{1})
       /\ (leaf_rel (predI C (predC1 c{1})) _h oram{1} oram{2})
      ).
      ecall (leaf_fetch C _h oram{1} oram{2} c{1}).
      + by auto => /> &1 &2 * /#.

      seq 1 1: (
          ={i, p}
       /\ c{1} = t{1}.`1 /\ v0{1} = t{1}.`2
       /\ pos{1} = p0{2}
       /\ size p0{2} = _h
       /\ (0 <= i{1} < size p{1})
       /\ (leaf_rel (predI C (predC1 c{1})) _h oram{1} oram{2})
      ).
      + by auto => />; by smt(supp_dlist_size).

      sp 1 0.
      seq 1 1: (
          ={i, p}
       /\ c{1} = t{1}.`1
       /\ pos{1} = p0{2}
       /\ (0 <= i{1} < size p{1})
       /\ (leaf_rel (predU C (pred1 c{1})) _h oram{1} oram{2})
      ).
      ecall (leaf_putback (predI C (predC1 c{1})) _h oram{1} oram{2} (c{1}, pos{1}, v0{1})).
      + auto => /> &1 &2 *; do! split.
        + move => *; do! split.
          + by smt().
          + move => *; do! split.
            + by move => @/predC1 @/"_.[_<-_]" /#.
            + by move => * /#.
          + move => 23? Hfull *; do! split.
            + by smt().
            + move => ? c1.
              have->: (predU C (pred1 t{1}.`1)) = (predU (predI C (predC1 t{1}.`1)) (pred1 t{1}.`1)) by smt().
              by have /# := Hfull c1.

      ecall (leaf_flush (predU C (pred1 c{1})) _h oram{1} oram{2}).
      + by auto => |> &1 &2 * /#.
  + auto => |> *; split.
    (* pre => inv *)
    + split.
      + by exact List.size_ge0.
      + by exists pred0; assumption.
    (* inv => post *)
    + move => 8?.
      admitted.
  (*     rewrite /leaf_rel /#. *)
  (* qed. *)
end SimpleORAM.
