require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array1 Array4 Array6 Array50 Array192 Array19200 BArray8 BArray32 BArray48
BArray400 BArray1536 BArray153600 SBArray48_32 SBArray1536_48
SBArray153600_1536.

module type Syscall_t = {
  proc randombytes_8 (_:BArray8.t) : BArray8.t
}.

module Syscall : Syscall_t = {
  proc randombytes_8 (a:BArray8.t) : BArray8.t = {

    a <$ BArray8.darray;
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc randombyte () : W64.t = {
    var aux:BArray8.t;
    var r:W64.t;
    var buf:BArray8.t;
    buf <- witness;
    aux <@ SC.randombytes_8 (buf);
    buf <- aux;
    r <- (BArray8.get64 buf 0);
    return r;
  }
  proc random (x:W64.t) : W64.t = {
    var ans:W64.t;
    ans <@ randombyte ();
    ans <- (ans \umod x);
    return ans;
  }
  proc bSR (x:W64.t) : W64.t = {
    var ans:W64.t;
    var aux:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    x <- x;
    ( _0,  _1,  _2,  _3,  _4, ans) <- (LZCNT_64 x);
    aux <- (W64.of_int 63);
    ans <- (aux - ans);
    ans <- ans;
    return ans;
  }
  proc isDesOf (j0:W64.t, j1:W64.t) : bool = {
    var b:bool;
    var ans:W64.t;
    var bitsj0:W64.t;
    var bitsj1:W64.t;
    var diff:W64.t;
    var j2:W64.t;
    var one:W64.t;
    ans <- (W64.of_int 0);
    if ((j0 \ult j1)) {
      bitsj0 <@ bSR (j0);
      bitsj1 <@ bSR (j1);
      diff <- (bitsj1 - bitsj0);
      j2 <- (j1 `>>` (truncateu8 (diff `&` (W64.of_int 63))));
      one <- (W64.of_int 1);
      ans <- ((j2 = j0) ? one : ans);
    } else {

    }
    b <- (ans = (W64.of_int 1));
    return b;
  }
  proc addToNode (node:BArray1536.t, nodeElem:BArray48.t) : BArray1536.t * W64.t list * W64.t list = {
    var i:W64.t;
    var pos:W64.t;
    var vals:BArray32.t;
    var k:W64.t;
    var flag:W8.t;
    var pk:W64.t;
    var this_nodeElem:BArray48.t;
    var this_i:W64.t;
    var b_cond:bool;
    var cond:W8.t;
    var this_pos:W64.t;
    var j:W64.t;
    var this_v:W64.t;
    var j_0:W64.t;
    var  _0:W64.t;
    var  _1:W64.t;
    var node_leakage:W64.t list;
    var nodeElem_leakage:W64.t list;
    node_leakage <- [];
    nodeElem_leakage <- [];
    this_nodeElem <- witness;
    vals <- witness;
    i <- (BArray48.get64 nodeElem 0);
    nodeElem_leakage <- W64.of_int 0 :: nodeElem_leakage;
    pos <- (BArray48.get64 nodeElem 1);
    nodeElem_leakage <- W64.of_int 1 :: nodeElem_leakage;
    vals <- (SBArray48_32.get_sub64 nodeElem 2);
    nodeElem_leakage <- W64.of_int 2 :: nodeElem_leakage;
    k <- (W64.of_int 0);
    flag <- (W8.of_int 1);
    while ((k \ult (W64.of_int 32))) {
      pk <- (k * (W64.of_int (2 + 4)));
      this_nodeElem <- (SBArray1536_48.get_sub64 node (W64.to_uint pk));
      this_i <- (BArray48.get64 this_nodeElem 0);
      node_leakage <- (pk + W64.of_int 0) :: node_leakage;
      b_cond <- (this_i = (W64.of_int (((200 + 4) - 1) %/ 4)));
      cond <- (SETcc b_cond);
      cond <- (cond `&` flag);
      if ((cond = (W8.of_int 1))) {
        this_nodeElem <- (BArray48.set64 this_nodeElem 0 i);
        node_leakage <- (pk + W64.of_int 0) :: node_leakage;
         _0 <- (BArray48.get64 this_nodeElem 1);
        node_leakage <- (pk + W64.of_int 1) :: node_leakage;
        this_nodeElem <- (BArray48.set64 this_nodeElem 1 pos);
        node_leakage <- (pk + W64.of_int 1) :: node_leakage;
        j_0 <- (W64.of_int 0);
        while ((j_0 \ult (W64.of_int 4))) {
           _1 <-
          (BArray48.get64 this_nodeElem (W64.to_uint ((W64.of_int 2) + j_0)));
          node_leakage <- (pk + W64.of_int 2 + j_0) :: node_leakage;
          this_nodeElem <-
          (BArray48.set64 this_nodeElem (W64.to_uint ((W64.of_int 2) + j_0))
          (BArray32.get64 vals (W64.to_uint j_0)));
          node_leakage <- (pk + W64.of_int 2 + j_0) :: node_leakage;
          nodeElem_leakage <- (W64.of_int 2 + j_0) :: node_leakage;
          j_0 <- (j_0 + (W64.of_int 1));
        }
        flag <- (W8.of_int 0);
      } else {
        this_nodeElem <- (BArray48.set64 this_nodeElem 0 this_i);
        node_leakage <- (pk + W64.of_int 0) :: node_leakage;
        this_pos <- (BArray48.get64 this_nodeElem 1);
        node_leakage <- (pk + W64.of_int 1) :: node_leakage;
        this_nodeElem <- (BArray48.set64 this_nodeElem 1 this_pos);
        node_leakage <- (pk + W64.of_int 1) :: node_leakage;
        j <- (W64.of_int 0);
        while ((j \ult (W64.of_int 4))) {
          this_v <-
          (BArray48.get64 this_nodeElem (W64.to_uint ((W64.of_int 2) + j)));
          node_leakage <- (pk + W64.of_int 2 + j) :: node_leakage;
           _0 <- (BArray32.get64 vals (W64.to_uint j));
          nodeElem_leakage <- (W64.of_int 2 + j) :: node_leakage;
          this_nodeElem <-
          (BArray48.set64 this_nodeElem (W64.to_uint ((W64.of_int 2) + j))
          this_v);
          node_leakage <- (pk + W64.of_int 2 + j) :: node_leakage;
          j <- (j + (W64.of_int 1));
        }
      }
      node <- (SBArray1536_48.set_sub64 node (W64.to_uint pk) this_nodeElem);
      k <- (k + (W64.of_int 1));
    }
    return (node, node_leakage, nodeElem_leakage);
  }
  proc false_addToNode (node:BArray1536.t, nodeElem:BArray48.t) : BArray1536.t * W64.t list * W64.t list = {
    var vals:BArray32.t;
    var k:W64.t;
    var pk:W64.t;
    var this_nodeElem:BArray48.t;
    var this_i:W64.t;
    var this_pos:W64.t;
    var j:W64.t;
    var this_v:W64.t;
    var  _0:W64.t;
    var  _1:W64.t;
    var  _2:W64.t;
    var node_leakage:W64.t list;
    var nodeElem_leakage:W64.t list;
    node_leakage <- [];
    nodeElem_leakage <- [];
    this_nodeElem <- witness;
    vals <- witness;
     _0 <- (BArray48.get64 nodeElem 0);
    nodeElem_leakage <- W64.of_int 0 :: nodeElem_leakage;
     _1 <- (BArray48.get64 nodeElem 1);
    nodeElem_leakage <- W64.of_int 1 :: nodeElem_leakage;
    vals <- (SBArray48_32.get_sub64 nodeElem 2);
    nodeElem_leakage <- W64.of_int 2 :: nodeElem_leakage;
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 32))) {
      pk <- (k * (W64.of_int (2 + 4)));
      this_nodeElem <- (SBArray1536_48.get_sub64 node (W64.to_uint pk));
      this_i <- (BArray48.get64 this_nodeElem 0);
      node_leakage <- (pk + W64.of_int 0) :: node_leakage;
      this_nodeElem <- (BArray48.set64 this_nodeElem 0 this_i);
      node_leakage <- (pk + W64.of_int 0) :: node_leakage;
      this_pos <- (BArray48.get64 this_nodeElem 1);
      node_leakage <- (pk + W64.of_int 1) :: node_leakage;
      this_nodeElem <- (BArray48.set64 this_nodeElem 1 this_pos);
      node_leakage <- (pk + W64.of_int 1) :: node_leakage;
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 4))) {
        this_v <-
        (BArray48.get64 this_nodeElem (W64.to_uint ((W64.of_int 2) + j)));
        node_leakage <- (pk + W64.of_int 2 + j) :: node_leakage;
         _2 <- (BArray32.get64 vals (W64.to_uint j));
        nodeElem_leakage <- (W64.of_int 2 + j) :: node_leakage;
        this_nodeElem <-
        (BArray48.set64 this_nodeElem (W64.to_uint ((W64.of_int 2) + j))
        this_v);
        node_leakage <- (pk + W64.of_int 2 + j) :: node_leakage;
        j <- (j + (W64.of_int 1));
      }
      node <- (SBArray1536_48.set_sub64 node (W64.to_uint pk) this_nodeElem);
      k <- (k + (W64.of_int 1));
    }
    return (node, node_leakage, nodeElem_leakage);
  }

  proc fetch(pos:BArray400.t, oram:BArray153600.t, res_0:BArray48.t, i:W64.t) : 
      BArray400.t * BArray153600.t * BArray48.t * W64.t * W64.t * W64.t list * W64.t list = {
    var ans_j:W64.t;
    var ans_k:W64.t;
    var ix:W64.t;
    var pi:W64.t;
    var node:BArray1536.t;
    var k:W64.t;
    var pk:W64.t;
    var nodeElem:BArray48.t;
    var this_i:W64.t;
    var idx:W64.t;
    var in_res:W64.t;
    var v:W64.t;
    var idx_0:W64.t;
    var v_0:W64.t;
    var  _0:W64.t;
    var oram_leakage:W64.t list;
    var res_0_leakage:W64.t list;
    oram_leakage <- [];
    res_0_leakage <- [];
    node <- witness;
    nodeElem <- witness;
    ans_j <- (W64.of_int 0);
    ans_k <- (W64.of_int 0);
    ix <- (BArray400.get64 pos (W64.to_uint i));
    ix <- (ix + (W64.of_int (((200 + 4) - 1) %/ 4)));
    while (((W64.of_int 0) \ult ix)) {
      pi <- ix;
      pi <- (pi * (W64.of_int (32 * (2 + 4))));
      node <- (SBArray153600_1536.get_sub64 oram (W64.to_uint pi));
      k <- (W64.of_int 0);
      while ((k \ult (W64.of_int 32))) {
        pk <- (k * (W64.of_int (2 + 4)));
        nodeElem <- (SBArray1536_48.get_sub64 node (W64.to_uint pk));
        this_i <- (BArray48.get64 nodeElem 0);
        oram_leakage <- (pi + pk + W64.of_int 0) :: oram_leakage;
        if ((this_i = i)) {
          ans_j <- ix;
          ans_k <- k;
          idx_0 <- (W64.of_int 0);
          while ((idx_0 \ult (W64.of_int (2 + 4)))) {
             _0 <- (BArray48.get64 res_0 (W64.to_uint idx_0));
            res_0_leakage <- idx_0 :: res_0_leakage;
            v_0 <- (BArray48.get64 nodeElem (W64.to_uint idx_0));
            oram_leakage <- (pi + pk + idx_0) :: oram_leakage;
            res_0 <- (BArray48.set64 res_0 (W64.to_uint idx_0) v_0);
            res_0_leakage <- idx_0 :: res_0_leakage;
            if ((idx_0 = (W64.of_int 0))) {
              nodeElem <-
              (BArray48.set64 nodeElem (W64.to_uint idx_0)
              (W64.of_int (((200 + 4) - 1) %/ 4)));
              oram_leakage <- (pi + pk + idx_0) :: oram_leakage;
            } else {
              nodeElem <-
              (BArray48.set64 nodeElem (W64.to_uint idx_0) (W64.of_int 0));
              oram_leakage <- (pi + pk + idx_0) :: oram_leakage;
            }
            idx_0 <- (idx_0 + (W64.of_int 1));
          }
        } else {
          idx <- (W64.of_int 0);
          while ((idx \ult (W64.of_int (2 + 4)))) {
            in_res <- (BArray48.get64 res_0 (W64.to_uint idx));
            res_0_leakage <- idx :: res_0_leakage;
            v <- (BArray48.get64 nodeElem (W64.to_uint idx));
            oram_leakage <- (pi + pk + idx) :: oram_leakage;
            res_0 <- (BArray48.set64 res_0 (W64.to_uint idx) in_res);
            res_0_leakage <- idx :: res_0_leakage;
            nodeElem <- (BArray48.set64 nodeElem (W64.to_uint idx) v);
            oram_leakage <- (pi + pk + idx) :: oram_leakage;
            idx <- (idx + (W64.of_int 1));
          }
        }
        node <- (SBArray1536_48.set_sub64 node (W64.to_uint pk) nodeElem);
        k <- (k + (W64.of_int 1));
      }
      oram <- (SBArray153600_1536.set_sub64 oram (W64.to_uint pi) node);
      ix <- (ix `>>` (W8.of_int 1));
    }
    return (pos, oram, res_0, ans_j, ans_k, oram_leakage, res_0_leakage);
  }
}.

module OnlyLeakage = {
  proc addToNode_leakage() : W64.t list * W64.t list = {
    var k:W64.t;
    var pk:W64.t;
    var j:W64.t;
    var node_leakage:W64.t list;
    var nodeElem_leakage:W64.t list;

    node_leakage <- [];
    nodeElem_leakage <- [];

    nodeElem_leakage <- W64.of_int 0 :: nodeElem_leakage;
    nodeElem_leakage <- W64.of_int 1 :: nodeElem_leakage;
    nodeElem_leakage <- W64.of_int 2 :: nodeElem_leakage;

    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 32))) {
      pk <- (k * (W64.of_int (2 + 4)));
      node_leakage <- (pk + W64.of_int 0) :: node_leakage;
      node_leakage <- (pk + W64.of_int 0) :: node_leakage;
      node_leakage <- (pk + W64.of_int 1) :: node_leakage;
      node_leakage <- (pk + W64.of_int 1) :: node_leakage;
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 4))) {
        node_leakage <- (pk + W64.of_int 2 + j) :: node_leakage;
        node_leakage <- (pk + W64.of_int 2 + j) :: node_leakage;
        nodeElem_leakage <- (W64.of_int 2 + j) :: node_leakage;
        j <- (j + (W64.of_int 1));
      }
      k <- (k + (W64.of_int 1));
    }
    return (node_leakage, nodeElem_leakage);
  }

  proc fetch_leakage(pos:BArray400.t, oram:BArray153600.t, res_0:BArray48.t, i:W64.t) : 
      W64.t list * W64.t list = {
    var ix:W64.t;
    var pi:W64.t;
    var k:W64.t;
    var pk:W64.t;
    var idx:W64.t;
    var oram_leakage:W64.t list;
    var res_0_leakage:W64.t list;
    oram_leakage <- [];
    res_0_leakage <- [];
    ix <- (BArray400.get64 pos (W64.to_uint i));
    ix <- (ix + (W64.of_int (((200 + 4) - 1) %/ 4)));
    while (((W64.of_int 0) \ult ix)) {
      pi <- ix;
      pi <- (pi * (W64.of_int (32 * (2 + 4))));
      k <- (W64.of_int 0);
      while ((k \ult (W64.of_int 32))) {
        pk <- (k * (W64.of_int (2 + 4)));
        oram_leakage <- (pi + pk + W64.of_int 0) :: oram_leakage;
        idx <- (W64.of_int 0);
        while ((idx \ult (W64.of_int (2 + 4)))) {
          res_0_leakage <- idx :: res_0_leakage;
          oram_leakage <- (pi + pk + idx) :: oram_leakage;
          res_0_leakage <- idx :: res_0_leakage;
          oram_leakage <- (pi + pk + idx) :: oram_leakage;
          idx <- (idx + (W64.of_int 1));
        }
        k <- (k + (W64.of_int 1));
      }
      ix <- (ix `>>` (W8.of_int 1));
    }
    return (oram_leakage, res_0_leakage);
  }
}.

module M2 = M(Syscall).

lemma leakage_addToNode :
  equiv[ M2.addToNode ~ OnlyLeakage.addToNode_leakage :
      true ==> res{1}.`2 = res{2}.`1
  ].
proof.
  proc.
  simplify.
  seq 12 6 : (={node_leakage, k}).
  - auto.
  while (={node_leakage, k}).
  - seq 7 2 : (={node_leakage, k, pk}).
    + auto.
    auto.
    if{1}.
    - seq 7 4 : (={node_leakage, k, pk} /\ j_0{1} = j{2}).
      auto.
      seq 1 1 : (={node_leakage, k, pk} /\ j_0{1} = j{2}).
      + while (={node_leakage, k, pk} /\ j_0{1} = j{2}).
        * auto.
        * skip.
          move => &m1 &m2 H.
          smt().
        * wp.
          skip.
          move => &m1 &m2 H.
          smt().
    - seq 7 4 : (={node_leakage, k, pk, j}).
      + auto.
      while (={node_leakage, k, pk, j}).
      * auto.
      * skip.
        move => &m1 &m2 H.
        smt().
      * skip.
        move => &m1 &m2 H.
        smt().
qed.

lemma leakage_false_addToNode :
  equiv[ M2.false_addToNode ~ OnlyLeakage.addToNode_leakage :
      true ==> res{1}.`2 = res{2}.`1
  ].
proof.
  proc.
  seq 11 6 : (={node_leakage, k}).
  - auto.
  while (={node_leakage, k}).
  - seq 11 6 : (={node_leakage, k, pk, j}).
    + auto.
    + seq 1 1 : (={node_leakage, k, pk, j}).
      * while (={node_leakage, k, pk, j}).
        auto.
      * auto.
    + auto.
  - auto.
qed.

lemma leakage_fetch :
  equiv[M2.fetch ~ OnlyLeakage.fetch_leakage :
    ={pos, i} ==> res{1}.`6 = res{2}.`1
  ].
proof.
  proc.
  seq 8 4 : (={pos, i, oram_leakage, ix}).
  - auto.
  while (={pos, i, oram_leakage, ix}).
  - seq 4 3 : (={pos, i, oram_leakage, ix, pi, k}).
    + auto.
    seq 1 1 : (={pos, i, oram_leakage, ix, pi, k}).
    + while (={pos, i, oram_leakage, ix, pi, k}).
      * seq 4 2 : (={pos, i, oram_leakage, ix, pi, k, pk}).
        - auto.
        if{1}.
        - seq 3 1 : (={pos, i, oram_leakage, ix, pi, k, pk} /\ idx_0{1} = idx{2}).
          + auto.
          seq 1 1 : (={pos, i, oram_leakage, ix, pi, k, pk} /\ idx_0{1} = idx{2}).
          + while (={pos, i, oram_leakage, ix, pi, k, pk} /\ idx_0{1} = idx{2}).
            * auto.
            auto.
          auto.
        - seq 1 1 : (={pos, i, oram_leakage, ix, pi, k, pk, idx}).
          + auto.
          seq 1 1 : (={pos, i, oram_leakage, ix, pi, k, pk, idx}).
          * while (={pos, i, oram_leakage, ix, pi, k, pk, idx}).
            - auto.
              skip.
              smt().
          * auto.
            skip.
            smt().
      * auto.
        skip.
        smt().
qed.
