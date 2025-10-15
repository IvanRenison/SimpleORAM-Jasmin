require import Oram.
require import SimpleORAM.


module Jasmin = M(Syscall).

clone SimpleORAM as EC_Model with
  type value <- W64.t,
  type cell <- W64.t.

type NodeElem = BArray48.t.
type Node = BArray1536.t.
type ORAM = BArray196608.t.
type PosArray = BArray512.t.
type PosArray_ORAM = PosArray * ORAM.

op eq_pos_path (pos : W64.t) (p : EC_Model.path) : bool =
  size p <= 64 /\ forall (i : int), 0 <= i < 64 => pos.[i] = nth false p i.
  

op eq_NodeElem_block (nodeElem : NodeElem) (b : EC_Model.path) : bool. (* TODO *)

op eq_Node_blocklist (node : Node) (b : EC_Model.block list) : bool. (* TODO *)

op eq_ORAM_buckets (joram : ORAM) (o : EC_Model.path -> EC_Model.block list) : bool. (* TODO *)

op eq_Pos_positions (Pos : PosArray) (positions : W64.t -> EC_Model.path) : bool. (* TODO *)

op eq_PosORAM_oram (Pos_joram : PosArray_ORAM) (oram : EC_Model.oram) : bool. (* TODO *)


type Query = W64.t * W64.t * W64.t.
type Queries = BArray2400.t.
type MultiQueryAns = BArray800.t.

op eq_Query_inst (q : Query) (i : EC_Model.inst) : bool. (* TODO *)
op eq_Queries_prog (queries : Queries) (p : EC_Model.prog) : bool. (* TODO *)
op eq_MultiQueryAns_valuelist (ans : MultiQueryAns) (os : W64.t list) : bool. (* TODO *)

op eq_JLeakage_leakagelist (jleak : JLeakage.leakage) (ecleak : EC_Model.leakage list) : bool. (* TODO *)


lemma functional_correctness :
  equiv[
    Jasmin.multiQuery ~ EC_Model.ORAM.compile :
      eq_PosORAM_oram (pos{1}, oram{1}) o{2}
      /\ eq_Queries_prog queries{1} p{2}
      ==> eq_JLeakage_leakagelist res{1}.`1 EC_Model.ORAM.leakage{2}
        /\ eq_MultiQueryAns_valuelist res{1}.`4 res{2}.`2
  ].




