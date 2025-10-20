require import AllCore IntDiv CoreMap List Distr.

require import Oram.
require import SimpleORAM.
require import SBArray48_32.
require import SBArray1536_48.
require import SBArray3200_32.
require import SBArray4800_48.
require import SBArray196608_1536.


from Jasmin require import JModel_x86.

module Jasmin = M(Syscall).

print SBArray48_32.get_sub64.

op n : int = 256.
op K : int = 32.
op b_sz : int = 4.
op N_queries : int = 100.

op N : int = 64.

clone SimpleORAM as EC_Model with
  type value <- BArray32.t,
  type cell <- W64.t,
  op K <- K.

type Block = BArray32.t.
type NodeElem = BArray48.t.
type Node = BArray1536.t.
type ORAM = BArray196608.t.
type PosArray = BArray512.t.
type PosArray_ORAM = PosArray * ORAM.

op Block_get (vs : Block) (j : int) : W64.t = BArray32.get64 vs j.
op NodeElem_i (elem : NodeElem) : W64.t = BArray48.get64 elem 0.
op NodeElem_pos (elem : NodeElem) : W64.t = BArray48.get64 elem 1.
op NodeElem_vals (elem : NodeElem) : BArray32.t = SBArray48_32.get_sub64 elem 2.
op NodeElem_get (elem : NodeElem) (j : int) : W64.t = BArray48.get64 elem (2 + j).
op Node_get (node : Node) (k : int) : NodeElem = SBArray1536_48.get_sub64 node k.
op ORAM_get (oram : ORAM) (ix : int) : Node = SBArray196608_1536.get_sub64 oram ix.
op PosArray_get (Pos : PosArray) (i : int) : W64.t = BArray512.get64 Pos i.

op eq_pos_path (pos : W64.t) (p : EC_Model.path) : bool =
  size p <= 64 /\ forall (i : int), 0 <= i < 64 => pos.[i] = nth false p i.

op pos_to_path (pos : W64.t) : EC_Model.path = EC_Model.int2path (W64.to_uint pos).
op path_to_pos (p : EC_Model.path) : W64.t = W64.of_int (EC_Model.path2int p).
  
op eq_NodeElem_tuple (nodeElem : NodeElem) (b : EC_Model.tuple) : bool =
  NodeElem_i nodeElem = b.`1
    /\ eq_pos_path (NodeElem_pos nodeElem) b.`2
    /\ NodeElem_vals nodeElem = b.`3.

op NodeElem_to_tuple (nodeElem : NodeElem) : EC_Model.tuple =
  (NodeElem_i nodeElem, pos_to_path (NodeElem_pos nodeElem), NodeElem_vals nodeElem).

op Node_to_NodeElemlist (node : Node) : NodeElem list =
  mkseq (fun i => (SBArray1536_48.get_sub64 node (i * 48))) K.
  
op Node_to_tuplelist (node : Node) : EC_Model.tuple list =
  map NodeElem_to_tuple
    (filter (fun nodeElem => W64.to_uint (NodeElem_i nodeElem) < N)
       (Node_to_NodeElemlist node)
    ).
  
op eq_Node_tuplelist (node : Node) (b : EC_Model.tuple list) : bool =
  perm_eq (Node_to_tuplelist node) b.

op eq_ORAM_buckets (joram : ORAM) (o : EC_Model.path -> EC_Model.tuple list) : bool =
  forall (ix : int), 0 <= ix < 2 * N =>
    eq_Node_tuplelist
      (SBArray196608_1536.get_sub64 joram (ix * (K + 2 + b_sz)))
      (o (EC_Model.int2path ix)).

op eq_Pos_positions (Pos : PosArray) (positions : W64.t -> EC_Model.path) : bool =
  forall (i : int), 0 <= i < N =>
    eq_pos_path (BArray512.get64 Pos i) (positions (W64.of_int i)).

print EC_Model.oram.

op eq_PosORAM_oram (Pos_joram : PosArray_ORAM) (or : EC_Model.oram) : bool =
  6 = or.`EC_Model.height
    /\ eq_Pos_positions Pos_joram.`1 or.`EC_Model.positions
    /\ eq_ORAM_buckets Pos_joram.`2 or.`EC_Model.bucket.


type BlockQuery = BArray48.t.
type BlockQueries = BArray4800.t.
type BlockMultiQueryAns = BArray3200.t.

op BlockQuery_get_ty (query : BlockQuery) : W64.t = BArray48.get64 query 0.
op BlockQuery_get_i (query : BlockQuery) : W64.t = BArray48.get64 query 1.
op BlockQuery_get_vals (query : BlockQuery) : BArray32.t = SBArray48_32.get_sub64 query 2.

op eq_BlockQuery_inst (query : BlockQuery) (i : EC_Model.inst) : bool =
  with i = EC_Model.Rd c =>
    (BlockQuery_get_ty query = W64.of_int 0
      /\ BlockQuery_get_i query = c)
  with i = EC_Model.Wt cv =>
    (BlockQuery_get_ty query = W64.of_int 1
      /\ BlockQuery_get_i query = cv.`1
      /\ BlockQuery_get_vals query = cv.`2).

op eq_BlockQueries_prog (queries : BlockQueries) (p : EC_Model.prog) : bool =
  size p = N_queries /\
  forall (q : int), 0 <= q < N_queries =>
    eq_BlockQuery_inst (SBArray4800_48.get_sub64 queries q) (nth (EC_Model.Rd (W64.of_int 0)) p q).

op eq_BlockMultiQueryAns_valuelist (ans : BlockMultiQueryAns) (os : BArray32.t list) : bool =
  size os = N_queries /\
  forall (q : int), 0 <= q < N_queries =>
    SBArray3200_32.get_sub64 ans q = nth witness os q.

op eq_JLeakage_leakagelist (jleak : JLeakage.leakage) (ecleak : EC_Model.leakage list) : bool. (* TODO *)


lemma functional_correctness :
  equiv[
    Jasmin.multiQuery_blocks ~ EC_Model.ORAM.compile :
      eq_PosORAM_oram (pos{1}, oram{1}) o{2}
      /\ eq_BlockQueries_prog queries{1} p{2}
      ==> (forall (p : EC_Model.path), !EC_Model.ORAM.overflow{2} p) =>
        eq_JLeakage_leakagelist res{1}.`1 EC_Model.ORAM.leakage{2}
        /\ eq_BlockMultiQueryAns_valuelist res{1}.`4 res{2}.`2
  ].




