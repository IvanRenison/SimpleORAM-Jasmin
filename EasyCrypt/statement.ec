require import AllCore IntDiv CoreMap List Distr.

require import Oram.
require import SimpleORAM.
require import SBArray48_32.
require import SBArray1536_48.
require import SBArray196608_1536.

from Jasmin require import JModel_x86.

module Jasmin = M(Syscall).

print SBArray48_32.get_sub64.

clone SimpleORAM as EC_Model with
  type value <- BArray32.t,
  type cell <- W64.t.

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

op eq_NodeElem_block (nodeElem : NodeElem) (b : EC_Model.block) : bool. (* TODO *)

op eq_Node_blocklist (node : Node) (b : EC_Model.block list) : bool. (* TODO *)

op eq_ORAM_buckets (joram : ORAM) (o : EC_Model.path -> EC_Model.block list) : bool. (* TODO *)

op eq_Pos_positions (Pos : PosArray) (positions : W64.t -> EC_Model.path) : bool. (* TODO *)

op eq_PosORAM_oram (Pos_joram : PosArray_ORAM) (oram : EC_Model.oram) : bool. (* TODO *)


type BlockQuery = W64.t * W64.t * Block.
type BlockQueries = BArray4800.t.
type BlockMultiQueryAns = BArray3200.t.

op eq_BlockQuery_inst (q : BlockQuery) (i : EC_Model.inst) : bool. (* TODO *)
op eq_BlockQueries_prog (queries : BlockQueries) (p : EC_Model.prog) : bool. (* TODO *)
op eq_BlockMultiQueryAns_valuelist (ans : BlockMultiQueryAns) (os : BArray32.t list) : bool. (* TODO *)

op eq_JLeakage_leakagelist (jleak : JLeakage.leakage) (ecleak : EC_Model.leakage list) : bool. (* TODO *)


lemma functional_correctness :
  equiv[
    Jasmin.multiQuery_blocks ~ EC_Model.ORAM.compile :
      eq_PosORAM_oram (pos{1}, oram{1}) o{2}
      /\ eq_BlockQueries_prog queries{1} p{2}
      ==> eq_JLeakage_leakagelist res{1}.`1 EC_Model.ORAM.leakage{2}
        /\ eq_BlockMultiQueryAns_valuelist res{1}.`4 res{2}.`2
  ].




