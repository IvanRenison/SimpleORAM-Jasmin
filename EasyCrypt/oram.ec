require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import JLeakage.

require import
Array1 Array4 Array6 Array64 Array100 Array192 Array300 Array400 Array600
Array24576 BArray8 BArray32 BArray48 BArray512 BArray800 BArray1536
BArray2400 BArray3200 BArray4800 BArray196608 SBArray48_32 SBArray3200_32
SBArray4800_32 SBArray1536_48 SBArray196608_1536.

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
  proc randombyte () : JLeakage.leakage * W64.t = {
    var aux:BArray8.t;
    var leak:JLeakage.leakages;
    var r:W64.t;
    var buf:BArray8.t;
    var r2:W64.t;
    buf <- witness;
    leak <- [];
    aux <@ SC.randombytes_8 (buf);
    buf <- aux;
    leak <- (leak ++ [(LeakList [(Leak_int 0)])]);
    r <- (BArray8.get64 buf 0);
    aux <@ SC.randombytes_8 (buf);
    buf <- aux;
    leak <- (leak ++ [(LeakList [(Leak_int 0)])]);
    r2 <- (BArray8.get64 buf 0);
    r2 <- (r2 `<<` (W8.of_int 8));
    r <- (r `|` r2);
    aux <@ SC.randombytes_8 (buf);
    buf <- aux;
    leak <- (leak ++ [(LeakList [(Leak_int 0)])]);
    r2 <- (BArray8.get64 buf 0);
    r2 <- (r2 `<<` (W8.of_int 16));
    r <- (r `|` r2);
    aux <@ SC.randombytes_8 (buf);
    buf <- aux;
    leak <- (leak ++ [(LeakList [(Leak_int 0)])]);
    r2 <- (BArray8.get64 buf 0);
    r2 <- (r2 `<<` (W8.of_int 24));
    r <- (r `|` r2);
    aux <@ SC.randombytes_8 (buf);
    buf <- aux;
    leak <- (leak ++ [(LeakList [(Leak_int 0)])]);
    r2 <- (BArray8.get64 buf 0);
    r2 <- (r2 `<<` (W8.of_int 32));
    r <- (r `|` r2);
    aux <@ SC.randombytes_8 (buf);
    buf <- aux;
    leak <- (leak ++ [(LeakList [(Leak_int 0)])]);
    r2 <- (BArray8.get64 buf 0);
    r2 <- (r2 `<<` (W8.of_int 40));
    r <- (r `|` r2);
    aux <@ SC.randombytes_8 (buf);
    buf <- aux;
    leak <- (leak ++ [(LeakList [(Leak_int 0)])]);
    r2 <- (BArray8.get64 buf 0);
    r2 <- (r2 `<<` (W8.of_int 48));
    r <- (r `|` r2);
    return ((LeakList leak), r);
  }
  proc random (x:W64.t) : JLeakage.leakage * W64.t = {
    var leak:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var ans:W64.t;
    leak <- [];
    (leak_c, ans) <@ randombyte ();
    leak <- (leak ++ [leak_c]);
    ans <- ans;
    ans <- (ans \umod x);
    return ((LeakList leak), ans);
  }
  proc bSR (x:W64.t) : JLeakage.leakage * W64.t = {
    var leak:JLeakage.leakages;
    var ans:W64.t;
    var aux:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    leak <- [];
    x <- x;
    ( _0,  _1,  _2,  _3,  _4, ans) <- (LZCNT_64 x);
    aux <- (W64.of_int 63);
    ans <- (aux - ans);
    ans <- ans;
    return ((LeakList leak), ans);
  }
  proc isDesOf (j0:W64.t, j1:W64.t) : JLeakage.leakage * W8.t = {
    var leak:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var cond:W8.t;
    var bitsj0:W64.t;
    var bitsj1:W64.t;
    var diff:W64.t;
    var j2:W64.t;
    var cond_b:bool;
    var cond2_b:bool;
    var cond2:W8.t;
    leak <- [];
    (leak_c, bitsj0) <@ bSR (j0);
    leak <- (leak ++ [leak_c]);
    (leak_c, bitsj1) <@ bSR (j1);
    leak <- (leak ++ [leak_c]);
    diff <- (bitsj1 - bitsj0);
    j2 <- j1;
    j2 <- (j2 `>>` (truncateu8 (diff `&` (W64.of_int 63))));
    cond_b <- (j0 \ult j1);
    cond <- (SETcc cond_b);
    cond2_b <- (j2 = j0);
    cond2 <- (SETcc cond2_b);
    cond <- (cond `&` cond2);
    return ((LeakList leak), cond);
  }
  proc addToNode (node:BArray1536.t, nodeElem:BArray48.t, real:W8.t) : 
  JLeakage.leakage * BArray1536.t = {
    var _b:JLeakage.leakages;
    var _b_0:JLeakage.leakages;
    var leak:JLeakage.leakages;
    var leak_0:JLeakage.leakages;
    var leak_1:JLeakage.leakages;
    var leak_cond:JLeakage.leakages;
    var leak_cond_0:JLeakage.leakages;
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
    var not_cond:W8.t;
    var new_i:W64.t;
    var new_pos:W64.t;
    var j:W64.t;
    var new_v:W64.t;
    var v:W64.t;
    this_nodeElem <- witness;
    vals <- witness;
    leak <- [];
    leak <- (leak ++ [(LeakList [(Leak_int 0)])]);
    i <- (BArray48.get64 nodeElem 0);
    leak <- (leak ++ [(LeakList [(Leak_int 1)])]);
    pos <- (BArray48.get64 nodeElem 1);
    leak <- (leak ++ [(LeakList [(Leak_int 2)])]);
    vals <- (SBArray48_32.get_sub64 nodeElem 2);
    k <- (W64.of_int 0);
    flag <- (W8.of_int 1);
    leak_cond <- [];
    _b <- [];
    leak_cond <-
    (leak_cond ++ [(LeakList [(Leak_bool (k \ult (W64.of_int 32)))])]);
    while ((k \ult (W64.of_int 32))) {
      leak_0 <- [];
      pk <- (k * (W64.of_int (2 + 4)));
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint pk))])]);
      this_nodeElem <- (SBArray1536_48.get_sub64 node (W64.to_uint pk));
      (* Erased call to spill *)
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int 0)])]);
      this_i <- (BArray48.get64 this_nodeElem 0);
      b_cond <- (this_i = (W64.of_int (((256 + 4) - 1) %/ 4)));
      cond <- (SETcc b_cond);
      cond <- (cond `&` flag);
      cond <- (cond `&` real);
      not_cond <- (W8.of_int 1);
      not_cond <- not_cond;
      not_cond <- (not_cond - cond);
      not_cond <- not_cond;
      flag <- flag;
      flag <- (flag `&` not_cond);
      flag <- flag;
      b_cond <- (cond = (W8.of_int 1));
      new_i <- this_i;
      new_i <- (b_cond ? i : new_i);
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int 0)])]);
      this_nodeElem <- (BArray48.set64 this_nodeElem 0 new_i);
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int 1)])]);
      new_pos <- (BArray48.get64 this_nodeElem 1);
      new_pos <- (b_cond ? pos : new_pos);
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int 1)])]);
      this_nodeElem <- (BArray48.set64 this_nodeElem 1 new_pos);
      j <- (W64.of_int 0);
      leak_cond_0 <- [];
      _b_0 <- [];
      leak_cond_0 <-
      (leak_cond_0 ++ [(LeakList [(Leak_bool (j \ult (W64.of_int 4)))])]);
      while ((j \ult (W64.of_int 4))) {
        leak_1 <- [];
        b_cond <- (cond = (W8.of_int 1));
        leak_1 <-
        (leak_1 ++
        [(LeakList [(Leak_int (W64.to_uint ((W64.of_int 2) + j)))])]);
        new_v <-
        (BArray48.get64 this_nodeElem (W64.to_uint ((W64.of_int 2) + j)));
        leak_1 <- (leak_1 ++ [(LeakList [(Leak_int (W64.to_uint j))])]);
        v <- (BArray32.get64 vals (W64.to_uint j));
        new_v <- (b_cond ? v : new_v);
        leak_1 <-
        (leak_1 ++
        [(LeakList [(Leak_int (W64.to_uint ((W64.of_int 2) + j)))])]);
        this_nodeElem <-
        (BArray48.set64 this_nodeElem (W64.to_uint ((W64.of_int 2) + j))
        new_v);
        j <- (j + (W64.of_int 1));
        _b_0 <- (_b_0 ++ [(LeakList leak_1)]);
        leak_cond_0 <-
        (leak_cond_0 ++ [(LeakList [(Leak_bool (j \ult (W64.of_int 4)))])]);
      }
      leak_0 <-
      (leak_0 ++ [(LeakList [(LeakList leak_cond_0); (LeakList _b_0)])]);
      (* Erased call to unspill *)
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint pk))])]);
      node <- (SBArray1536_48.set_sub64 node (W64.to_uint pk) this_nodeElem);
      k <- (k + (W64.of_int 1));
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <-
      (leak_cond ++ [(LeakList [(Leak_bool (k \ult (W64.of_int 32)))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    return ((LeakList leak), node);
  }
  proc fetch (pos:BArray512.t, oram:BArray196608.t, res_0:BArray48.t, i:W64.t) : 
  JLeakage.leakage * BArray512.t * BArray196608.t * BArray48.t * W64.t *
  W64.t = {
    var _b:JLeakage.leakages;
    var _b_0:JLeakage.leakages;
    var _b_1:JLeakage.leakages;
    var leak:JLeakage.leakages;
    var leak_0:JLeakage.leakages;
    var leak_1:JLeakage.leakages;
    var leak_2:JLeakage.leakages;
    var leak_cond:JLeakage.leakages;
    var leak_cond_0:JLeakage.leakages;
    var leak_cond_1:JLeakage.leakages;
    var ans_j:W64.t;
    var ans_k:W64.t;
    var ix:W64.t;
    var pi:W64.t;
    var node:BArray1536.t;
    var k:W64.t;
    var pk:W64.t;
    var nodeElem:BArray48.t;
    var this_i:W64.t;
    var cond_b:bool;
    var idx:W64.t;
    var in_res:W64.t;
    var v:W64.t;
    var new_res:W64.t;
    var zero:W64.t;
    var new_i:W64.t;
    var n_reg:W64.t;
    node <- witness;
    nodeElem <- witness;
    leak <- [];
    ans_j <- (W64.of_int 0);
    ans_k <- (W64.of_int 0);
    i <- i;
    leak <- (leak ++ [(LeakList [(Leak_int (W64.to_uint i))])]);
    ix <- (BArray512.get64 pos (W64.to_uint i));
    ix <- (ix + (W64.of_int (((256 + 4) - 1) %/ 4)));
    leak_cond <- [];
    _b <- [];
    leak_cond <-
    (leak_cond ++ [(LeakList [(Leak_bool ((W64.of_int 0) \ult ix))])]);
    while (((W64.of_int 0) \ult ix)) {
      leak_0 <- [];
      pi <- ix;
      pi <- (pi * (W64.of_int (32 * (2 + 4))));
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint pi))])]);
      node <- (SBArray196608_1536.get_sub64 oram (W64.to_uint pi));
      (* Erased call to spill *)
      k <- (W64.of_int 0);
      leak_cond_0 <- [];
      _b_0 <- [];
      leak_cond_0 <-
      (leak_cond_0 ++ [(LeakList [(Leak_bool (k \ult (W64.of_int 32)))])]);
      while ((k \ult (W64.of_int 32))) {
        leak_1 <- [];
        pk <- (k * (W64.of_int (2 + 4)));
        leak_1 <- (leak_1 ++ [(LeakList [(Leak_int (W64.to_uint pk))])]);
        nodeElem <- (SBArray1536_48.get_sub64 node (W64.to_uint pk));
        leak_1 <- (leak_1 ++ [(LeakList [(Leak_int 0)])]);
        this_i <- (BArray48.get64 nodeElem 0);
        cond_b <- (this_i = i);
        ans_j <- (cond_b ? ix : ans_j);
        ans_k <- (cond_b ? k : ans_k);
        idx <- (W64.of_int 0);
        leak_cond_1 <- [];
        _b_1 <- [];
        leak_cond_1 <-
        (leak_cond_1 ++
        [(LeakList [(Leak_bool (idx \ult (W64.of_int (2 + 4))))])]);
        while ((idx \ult (W64.of_int (2 + 4)))) {
          leak_2 <- [];
          cond_b <- (this_i = i);
          (* Erased call to spill *)
          leak_2 <- (leak_2 ++ [(LeakList [(Leak_int (W64.to_uint idx))])]);
          in_res <- (BArray48.get64 res_0 (W64.to_uint idx));
          leak_2 <- (leak_2 ++ [(LeakList [(Leak_int (W64.to_uint idx))])]);
          v <- (BArray48.get64 nodeElem (W64.to_uint idx));
          new_res <- in_res;
          new_res <- (cond_b ? v : new_res);
          zero <- (W64.of_int 0);
          v <- (cond_b ? zero : v);
          leak_2 <- (leak_2 ++ [(LeakList [(Leak_int (W64.to_uint idx))])]);
          res_0 <- (BArray48.set64 res_0 (W64.to_uint idx) new_res);
          leak_2 <- (leak_2 ++ [(LeakList [(Leak_int (W64.to_uint idx))])]);
          nodeElem <- (BArray48.set64 nodeElem (W64.to_uint idx) v);
          idx <- (idx + (W64.of_int 1));
          (* Erased call to unspill *)
          _b_1 <- (_b_1 ++ [(LeakList leak_2)]);
          leak_cond_1 <-
          (leak_cond_1 ++
          [(LeakList [(Leak_bool (idx \ult (W64.of_int (2 + 4))))])]);
        }
        leak_1 <-
        (leak_1 ++ [(LeakList [(LeakList leak_cond_1); (LeakList _b_1)])]);
        cond_b <- (this_i = i);
        new_i <- this_i;
        n_reg <- (W64.of_int (((256 + 4) - 1) %/ 4));
        new_i <- (cond_b ? n_reg : new_i);
        leak_1 <- (leak_1 ++ [(LeakList [(Leak_int 0)])]);
        nodeElem <- (BArray48.set64 nodeElem 0 new_i);
        leak_1 <- (leak_1 ++ [(LeakList [(Leak_int (W64.to_uint pk))])]);
        node <- (SBArray1536_48.set_sub64 node (W64.to_uint pk) nodeElem);
        k <- (k + (W64.of_int 1));
        _b_0 <- (_b_0 ++ [(LeakList leak_1)]);
        leak_cond_0 <-
        (leak_cond_0 ++ [(LeakList [(Leak_bool (k \ult (W64.of_int 32)))])]);
      }
      leak_0 <-
      (leak_0 ++ [(LeakList [(LeakList leak_cond_0); (LeakList _b_0)])]);
      (* Erased call to unspill *)
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint pi))])]);
      oram <- (SBArray196608_1536.set_sub64 oram (W64.to_uint pi) node);
      ix <- (ix `>>` (W8.of_int 1));
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <-
      (leak_cond ++ [(LeakList [(Leak_bool ((W64.of_int 0) \ult ix))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    return ((LeakList leak), pos, oram, res_0, ans_j, ans_k);
  }
  proc fetch_export (pos:BArray512.t, oram:BArray196608.t, res_0:BArray48.t,
                     i:W64.t) : JLeakage.leakage * BArray512.t *
                                BArray196608.t * BArray48.t * W64.t * W64.t = {
    var leak:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var ans_j:W64.t;
    var ans_k:W64.t;
    leak <- [];
    pos <- pos;
    oram <- oram;
    res_0 <- res_0;
    i <- i;
    (leak_c, pos, oram, res_0, ans_j, ans_k) <@ fetch (pos, oram, res_0, i);
    leak <- (leak ++ [leak_c]);
    ans_j <- ans_j;
    ans_k <- ans_k;
    return ((LeakList leak), pos, oram, res_0, ans_j, ans_k);
  }
  proc pushDown (oram:BArray196608.t) : JLeakage.leakage * BArray196608.t = {
    var _b:JLeakage.leakages;
    var _b_0:JLeakage.leakages;
    var leak:JLeakage.leakages;
    var leak_0:JLeakage.leakages;
    var leak_1:JLeakage.leakages;
    var leak_2:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var leak_cond:JLeakage.leakages;
    var leak_cond_0:JLeakage.leakages;
    var n_reg:W64.t;
    var ix0:W64.t;
    var l:W64.t;
    var k:W64.t;
    var ik:W64.t;
    var toAdd:BArray1536.t;
    var ix:W64.t;
    var pi:W64.t;
    var node:BArray1536.t;
    var k_0:W64.t;
    var ik_0:W64.t;
    var i:W64.t;
    var b_cond:bool;
    var cond:W8.t;
    var this_nodeElem_toAdd:BArray48.t;
    var next_l:W64.t;
    var next_ix:W64.t;
    var ik_1:W64.t;
    var this_i:W64.t;
    var this_pos:W64.t;
    var this_nodeElem:BArray48.t;
    var this_pos_ix:W64.t;
    var isDes:W8.t;
    var cond_b:bool;
    var cond_0:W8.t;
    var new_i:W64.t;
    var n_reg_0:W64.t;
    node <- witness;
    this_nodeElem <- witness;
    this_nodeElem_toAdd <- witness;
    toAdd <- witness;
    leak <- [];
    n_reg <- (W64.of_int (((256 + 4) - 1) %/ 4));
    (leak_c, ix0) <@ random (n_reg);
    leak <- (leak ++ [leak_c]);
    ix0 <- (ix0 + (W64.of_int (((256 + 4) - 1) %/ 4)));
    (leak_c, l) <@ bSR (ix0);
    leak <- (leak ++ [leak_c]);
    l <- (l + (W64.of_int 1));
    k <- (W64.of_int 0);
    leak_cond <- [];
    _b <- [];
    leak_cond <-
    (leak_cond ++ [(LeakList [(Leak_bool (k \ult (W64.of_int 32)))])]);
    while ((k \ult (W64.of_int 32))) {
      leak_0 <- [];
      ik <- (k * (W64.of_int (2 + 4)));
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint ik))])]);
      toAdd <-
      (BArray1536.set64 toAdd (W64.to_uint ik)
      (W64.of_int (((256 + 4) - 1) %/ 4)));
      k <- (k + (W64.of_int 1));
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <-
      (leak_cond ++ [(LeakList [(Leak_bool (k \ult (W64.of_int 32)))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    leak_cond <- [];
    _b <- [];
    leak_cond <-
    (leak_cond ++ [(LeakList [(Leak_bool ((W64.of_int 0) \ult l))])]);
    while (((W64.of_int 0) \ult l)) {
      leak_0 <- [];
      l <- (l - (W64.of_int 1));
      l <- l;
      (* Erased call to spill *)
      ix <- ix0;
      ix <- (ix `>>` (truncateu8 (l `&` (W64.of_int 63))));
      pi <- (ix * (W64.of_int (32 * (2 + 4))));
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint pi))])]);
      node <- (SBArray196608_1536.get_sub64 oram (W64.to_uint pi));
      (* Erased call to spill *)
      k_0 <- (W64.of_int 0);
      leak_cond_0 <- [];
      _b_0 <- [];
      leak_cond_0 <-
      (leak_cond_0 ++ [(LeakList [(Leak_bool (k_0 \ult (W64.of_int 32)))])]);
      while ((k_0 \ult (W64.of_int 32))) {
        leak_1 <- [];
        ik_0 <- (k_0 * (W64.of_int (2 + 4)));
        (* Erased call to spill *)
        leak_1 <- (leak_1 ++ [(LeakList [(Leak_int (W64.to_uint ik_0))])]);
        i <- (BArray1536.get64 toAdd (W64.to_uint ik_0));
        b_cond <- (i <> (W64.of_int (((256 + 4) - 1) %/ 4)));
        cond <- (SETcc b_cond);
        leak_1 <- (leak_1 ++ [(LeakList [(Leak_int (W64.to_uint ik_0))])]);
        this_nodeElem_toAdd <-
        (SBArray1536_48.get_sub64 toAdd (W64.to_uint ik_0));
        node <- node;
        (leak_c, node) <@ addToNode (node, this_nodeElem_toAdd, cond);
        leak_1 <- (leak_1 ++ [leak_c]);
        node <- node;
        leak_1 <- (leak_1 ++ [(LeakList [(Leak_int (W64.to_uint ik_0))])]);
        toAdd <-
        (BArray1536.set64 toAdd (W64.to_uint ik_0)
        (W64.of_int (((256 + 4) - 1) %/ 4)));
        (* Erased call to unspill *)
        k_0 <- (k_0 + (W64.of_int 1));
        _b_0 <- (_b_0 ++ [(LeakList leak_1)]);
        leak_cond_0 <-
        (leak_cond_0 ++
        [(LeakList [(Leak_bool (k_0 \ult (W64.of_int 32)))])]);
      }
      leak_0 <-
      (leak_0 ++ [(LeakList [(LeakList leak_cond_0); (LeakList _b_0)])]);
      (* Erased call to unspill *)
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_bool (l <> (W64.of_int 0)))])]);
      if ((l <> (W64.of_int 0))) {
        leak_1 <- [];
        (* Erased call to spill *)
        next_l <- l;
        next_l <- (next_l - (W64.of_int 1));
        next_ix <- ix0;
        next_ix <- (next_ix `>>` (truncateu8 (next_l `&` (W64.of_int 63))));
        (* Erased call to unspill *)
        (* Erased call to spill *)
        k_0 <- (W64.of_int 0);
        leak_cond_0 <- [];
        _b_0 <- [];
        leak_cond_0 <-
        (leak_cond_0 ++
        [(LeakList [(Leak_bool (k_0 \ult (W64.of_int 32)))])]);
        while ((k_0 \ult (W64.of_int 32))) {
          leak_2 <- [];
          ik_1 <- (k_0 * (W64.of_int (2 + 4)));
          (* Erased call to spill *)
          leak_2 <- (leak_2 ++ [(LeakList [(Leak_int (W64.to_uint ik_1))])]);
          this_i <- (BArray1536.get64 node (W64.to_uint ik_1));
          leak_2 <-
          (leak_2 ++
          [(LeakList [(Leak_int (W64.to_uint (ik_1 + (W64.of_int 1))))])]);
          this_pos <-
          (BArray1536.get64 node (W64.to_uint (ik_1 + (W64.of_int 1))));
          leak_2 <- (leak_2 ++ [(LeakList [(Leak_int (W64.to_uint ik_1))])]);
          this_nodeElem <-
          (SBArray1536_48.get_sub64 node (W64.to_uint ik_1));
          (* Erased call to spill *)
          this_pos_ix <- this_pos;
          this_pos_ix <- (this_pos_ix + (W64.of_int (((256 + 4) - 1) %/ 4)));
          (leak_c, isDes) <@ isDesOf (next_ix, this_pos_ix);
          leak_2 <- (leak_2 ++ [leak_c]);
          cond_b <- (this_i <> (W64.of_int (((256 + 4) - 1) %/ 4)));
          cond_0 <- (SETcc cond_b);
          cond_0 <- (cond_0 `&` isDes);
          (leak_c, toAdd) <@ addToNode (toAdd, this_nodeElem, cond_0);
          leak_2 <- (leak_2 ++ [leak_c]);
          new_i <- this_i;
          cond_b <- (cond_0 = (W8.of_int 1));
          n_reg_0 <- (W64.of_int (((256 + 4) - 1) %/ 4));
          new_i <- (cond_b ? n_reg_0 : new_i);
          (* Erased call to unspill *)
          leak_2 <- (leak_2 ++ [(LeakList [(Leak_int (W64.to_uint ik_1))])]);
          node <- (BArray1536.set64 node (W64.to_uint ik_1) new_i);
          (* Erased call to unspill *)
          k_0 <- (k_0 + (W64.of_int 1));
          _b_0 <- (_b_0 ++ [(LeakList leak_2)]);
          leak_cond_0 <-
          (leak_cond_0 ++
          [(LeakList [(Leak_bool (k_0 \ult (W64.of_int 32)))])]);
        }
        leak_1 <-
        (leak_1 ++ [(LeakList [(LeakList leak_cond_0); (LeakList _b_0)])]);
        (* Erased call to unspill *)
        leak_0 <- (leak_0 ++ [(LeakList leak_1)]);
      } else {
        leak_1 <- [];
        leak_0 <- (leak_0 ++ [(LeakList leak_1)]);
      }
      (* Erased call to unspill *)
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint pi))])]);
      oram <- (SBArray196608_1536.set_sub64 oram (W64.to_uint pi) node);
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <-
      (leak_cond ++ [(LeakList [(Leak_bool ((W64.of_int 0) \ult l))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    return ((LeakList leak), oram);
  }
  proc pushDown_export (oram:BArray196608.t) : JLeakage.leakage *
                                               BArray196608.t = {
    var leak:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    leak <- [];
    oram <- oram;
    (leak_c, oram) <@ pushDown (oram);
    leak <- (leak ++ [leak_c]);
    return ((LeakList leak), oram);
  }
  proc initORAM (pos:BArray512.t, oram:BArray196608.t) : JLeakage.leakage *
                                                         BArray512.t *
                                                         BArray196608.t = {
    var _b:JLeakage.leakages;
    var _b_0:JLeakage.leakages;
    var leak:JLeakage.leakages;
    var leak_0:JLeakage.leakages;
    var leak_1:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var leak_cond:JLeakage.leakages;
    var leak_cond_0:JLeakage.leakages;
    var n2K:W64.t;
    var ix:W64.t;
    var pi:W64.t;
    var i:W64.t;
    var n_reg:W64.t;
    var pos_0:W64.t;
    var nodeElem_mem:BArray48.t;
    var l:W64.t;
    var nodeElem:BArray48.t;
    var root_node:BArray1536.t;
    var tr:W8.t;
    nodeElem <- witness;
    nodeElem_mem <- witness;
    root_node <- witness;
    leak <- [];
    n2K <- (W64.of_int (((((256 + 4) - 1) %/ 4) * 2) * 32));
    ix <- (W64.of_int 0);
    leak_cond <- [];
    _b <- [];
    leak_cond <- (leak_cond ++ [(LeakList [(Leak_bool (ix \ult n2K))])]);
    while ((ix \ult n2K)) {
      leak_0 <- [];
      pi <- (ix * (W64.of_int (2 + 4)));
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint pi))])]);
      oram <-
      (BArray196608.set64 oram (W64.to_uint pi)
      (W64.of_int (((256 + 4) - 1) %/ 4)));
      ix <- (ix + (W64.of_int 1));
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <- (leak_cond ++ [(LeakList [(Leak_bool (ix \ult n2K))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    i <- (W64.of_int 0);
    leak_cond <- [];
    _b <- [];
    leak_cond <-
    (leak_cond ++
    [(LeakList [(Leak_bool (i \ult (W64.of_int (((256 + 4) - 1) %/ 4))))])]);
    while ((i \ult (W64.of_int (((256 + 4) - 1) %/ 4)))) {
      leak_0 <- [];
      n_reg <- (W64.of_int (((256 + 4) - 1) %/ 4));
      (leak_c, pos_0) <@ random (n_reg);
      leak_0 <- (leak_0 ++ [leak_c]);
      pos_0 <- pos_0;
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint i))])]);
      pos <- (BArray512.set64 pos (W64.to_uint i) pos_0);
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int 0)])]);
      nodeElem_mem <- (BArray48.set64 nodeElem_mem 0 i);
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int 1)])]);
      nodeElem_mem <- (BArray48.set64 nodeElem_mem 1 pos_0);
      l <- (W64.of_int 2);
      leak_cond_0 <- [];
      _b_0 <- [];
      leak_cond_0 <-
      (leak_cond_0 ++
      [(LeakList [(Leak_bool (l \ult (W64.of_int (2 + 4))))])]);
      while ((l \ult (W64.of_int (2 + 4)))) {
        leak_1 <- [];
        leak_1 <- (leak_1 ++ [(LeakList [(Leak_int (W64.to_uint l))])]);
        nodeElem_mem <-
        (BArray48.set64 nodeElem_mem (W64.to_uint l) (W64.of_int 0));
        l <- (l + (W64.of_int 1));
        _b_0 <- (_b_0 ++ [(LeakList leak_1)]);
        leak_cond_0 <-
        (leak_cond_0 ++
        [(LeakList [(Leak_bool (l \ult (W64.of_int (2 + 4))))])]);
      }
      leak_0 <-
      (leak_0 ++ [(LeakList [(LeakList leak_cond_0); (LeakList _b_0)])]);
      nodeElem <- nodeElem_mem;
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (32 * (2 + 4)))])]);
      root_node <- (SBArray196608_1536.get_sub64 oram (32 * (2 + 4)));
      (* Erased call to spill *)
      (* Erased call to spill *)
      (* Erased call to spill *)
      tr <- (W8.of_int 1);
      (leak_c, root_node) <@ addToNode (root_node, nodeElem, tr);
      leak_0 <- (leak_0 ++ [leak_c]);
      (* Erased call to unspill *)
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (32 * (2 + 4)))])]);
      oram <- (SBArray196608_1536.set_sub64 oram (32 * (2 + 4)) root_node);
      (leak_c, oram) <@ pushDown (oram);
      leak_0 <- (leak_0 ++ [leak_c]);
      (* Erased call to unspill *)
      (* Erased call to unspill *)
      i <- (i + (W64.of_int 1));
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <-
      (leak_cond ++
      [(LeakList [(Leak_bool (i \ult (W64.of_int (((256 + 4) - 1) %/ 4))))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    return ((LeakList leak), pos, oram);
  }
  proc initORAM_export (pos:BArray512.t, oram:BArray196608.t) : JLeakage.leakage *
                                                                BArray512.t *
                                                                BArray196608.t = {
    var leak:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    leak <- [];
    pos <- pos;
    oram <- oram;
    (leak_c, pos, oram) <@ initORAM (pos, oram);
    leak <- (leak ++ [leak_c]);
    return ((LeakList leak), pos, oram);
  }
  proc read_write (pos:BArray512.t, oram:BArray196608.t, in_0:W64.t, v:W64.t,
                   wr:W8.t) : JLeakage.leakage * BArray512.t *
                              BArray196608.t * W64.t = {
    var _b:JLeakage.leakages;
    var leak:JLeakage.leakages;
    var leak_0:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var leak_cond:JLeakage.leakages;
    var ans:W64.t;
    var i:W64.t;
    var j:W64.t;
    var res_0:BArray48.t;
    var res_p:BArray48.t;
    var ji:W64.t;
    var new_v:W64.t;
    var cond_b:bool;
    var cond:W8.t;
    var write:W8.t;
    var write_b:bool;
    var n_reg:W64.t;
    var new_pos:W64.t;
    var root_node:BArray1536.t;
    var tr:W8.t;
    var  _0:W64.t;
    var  _1:W64.t;
    res_0 <- witness;
    res_p <- witness;
    root_node <- witness;
    leak <- [];
    i <- in_0;
    i <- (i `>>` (W8.of_int 2));
    i <- i;
    j <- in_0;
    j <- (j `&` (W64.of_int (4 - 1)));
    res_p <- res_0;
    (* Erased call to spill *)
    (* Erased call to spill *)
    (* Erased call to spill *)
    (leak_c, pos, oram, res_p,  _0,  _1) <@ fetch (pos, oram, res_p, i);
    leak <- (leak ++ [leak_c]);
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (* Erased call to spill *)
    ji <- (W64.of_int 0);
    leak_cond <- [];
    _b <- [];
    leak_cond <-
    (leak_cond ++ [(LeakList [(Leak_bool (ji \ult (W64.of_int 4)))])]);
    while ((ji \ult (W64.of_int 4))) {
      leak_0 <- [];
      leak_0 <-
      (leak_0 ++
      [(LeakList [(Leak_int (W64.to_uint ((W64.of_int 2) + ji)))])]);
      new_v <- (BArray48.get64 res_p (W64.to_uint ((W64.of_int 2) + ji)));
      cond_b <- (ji = j);
      ans <- (cond_b ? new_v : ans);
      cond <- (SETcc cond_b);
      write <- (cond `&` wr);
      write_b <- (write = (W8.of_int 1));
      new_v <- (write_b ? v : new_v);
      leak_0 <-
      (leak_0 ++
      [(LeakList [(Leak_int (W64.to_uint ((W64.of_int 2) + ji)))])]);
      res_p <-
      (BArray48.set64 res_p (W64.to_uint ((W64.of_int 2) + ji)) new_v);
      ji <- (ji + (W64.of_int 1));
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <-
      (leak_cond ++ [(LeakList [(Leak_bool (ji \ult (W64.of_int 4)))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    (* Erased call to spill *)
    (* Erased call to spill *)
    (* Erased call to spill *)
    n_reg <- (W64.of_int (((256 + 4) - 1) %/ 4));
    (leak_c, new_pos) <@ random (n_reg);
    leak <- (leak ++ [leak_c]);
    new_pos <- new_pos;
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    leak <- (leak ++ [(LeakList [(Leak_int 1)])]);
    res_p <- (BArray48.set64 res_p 1 new_pos);
    i <- i;
    (* Erased call to unspill *)
    leak <- (leak ++ [(LeakList [(Leak_int (W64.to_uint i))])]);
    pos <- (BArray512.set64 pos (W64.to_uint i) new_pos);
    (* Erased call to unspill *)
    leak <- (leak ++ [(LeakList [(Leak_int (32 * (2 + 4)))])]);
    root_node <- (SBArray196608_1536.get_sub64 oram (32 * (2 + 4)));
    (* Erased call to spill *)
    (* Erased call to spill *)
    res_p <- res_p;
    tr <- (W8.of_int 1);
    (leak_c, root_node) <@ addToNode (root_node, res_p, tr);
    leak <- (leak ++ [leak_c]);
    (* Erased call to unspill *)
    leak <- (leak ++ [(LeakList [(Leak_int (32 * (2 + 4)))])]);
    oram <- (SBArray196608_1536.set_sub64 oram (32 * (2 + 4)) root_node);
    (leak_c, oram) <@ pushDown (oram);
    leak <- (leak ++ [leak_c]);
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    return ((LeakList leak), pos, oram, ans);
  }
  proc read_write_export (pos:BArray512.t, oram:BArray196608.t, in_0:W64.t,
                          v:W64.t, wr:W8.t) : JLeakage.leakage *
                                              BArray512.t * BArray196608.t *
                                              W64.t = {
    var leak:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var ans:W64.t;
    leak <- [];
    pos <- pos;
    oram <- oram;
    in_0 <- in_0;
    v <- v;
    wr <- wr;
    (leak_c, pos, oram, ans) <@ read_write (pos, oram, in_0, v, wr);
    leak <- (leak ++ [leak_c]);
    pos <- pos;
    oram <- oram;
    ans <- ans;
    return ((LeakList leak), pos, oram, ans);
  }
  proc read_write_block (pos:BArray512.t, oram:BArray196608.t,
                         ans:BArray32.t, i:W64.t, vals:BArray32.t, wr:W8.t) : 
  JLeakage.leakage * BArray512.t * BArray196608.t * BArray32.t = {
    var _b:JLeakage.leakages;
    var leak:JLeakage.leakages;
    var leak_0:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var leak_cond:JLeakage.leakages;
    var res_0:BArray48.t;
    var res_p:BArray48.t;
    var j:W64.t;
    var new_v:W64.t;
    var v:W64.t;
    var wr_b:bool;
    var n_reg:W64.t;
    var new_pos:W64.t;
    var root_node:BArray1536.t;
    var tr:W8.t;
    var  _0:W64.t;
    var  _1:W64.t;
    res_0 <- witness;
    res_p <- witness;
    root_node <- witness;
    leak <- [];
    res_p <- res_0;
    (* Erased call to spill *)
    (* Erased call to spill *)
    (leak_c, pos, oram, res_p,  _0,  _1) <@ fetch (pos, oram, res_p, i);
    leak <- (leak ++ [leak_c]);
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    (* Erased call to spill *)
    (* Erased call to spill *)
    j <- (W64.of_int 0);
    leak_cond <- [];
    _b <- [];
    leak_cond <-
    (leak_cond ++ [(LeakList [(Leak_bool (j \ult (W64.of_int 4)))])]);
    while ((j \ult (W64.of_int 4))) {
      leak_0 <- [];
      leak_0 <-
      (leak_0 ++
      [(LeakList [(Leak_int (W64.to_uint ((W64.of_int 2) + j)))])]);
      new_v <- (BArray48.get64 res_p (W64.to_uint ((W64.of_int 2) + j)));
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint j))])]);
      ans <- (BArray32.set64 ans (W64.to_uint j) new_v);
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint j))])]);
      v <- (BArray32.get64 vals (W64.to_uint j));
      wr_b <- (wr = (W8.of_int 1));
      new_v <- (wr_b ? v : new_v);
      leak_0 <-
      (leak_0 ++
      [(LeakList [(Leak_int (W64.to_uint ((W64.of_int 2) + j)))])]);
      res_p <-
      (BArray48.set64 res_p (W64.to_uint ((W64.of_int 2) + j)) new_v);
      j <- (j + (W64.of_int 1));
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <-
      (leak_cond ++ [(LeakList [(Leak_bool (j \ult (W64.of_int 4)))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    (* Erased call to spill *)
    (* Erased call to spill *)
    (* Erased call to spill *)
    n_reg <- (W64.of_int (((256 + 4) - 1) %/ 4));
    (leak_c, new_pos) <@ random (n_reg);
    leak <- (leak ++ [leak_c]);
    new_pos <- new_pos;
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    leak <- (leak ++ [(LeakList [(Leak_int 1)])]);
    res_p <- (BArray48.set64 res_p 1 new_pos);
    i <- i;
    (* Erased call to unspill *)
    leak <- (leak ++ [(LeakList [(Leak_int (W64.to_uint i))])]);
    pos <- (BArray512.set64 pos (W64.to_uint i) new_pos);
    (* Erased call to unspill *)
    leak <- (leak ++ [(LeakList [(Leak_int (32 * (2 + 4)))])]);
    root_node <- (SBArray196608_1536.get_sub64 oram (32 * (2 + 4)));
    (* Erased call to spill *)
    (* Erased call to spill *)
    res_p <- res_p;
    tr <- (W8.of_int 1);
    (leak_c, root_node) <@ addToNode (root_node, res_p, tr);
    leak <- (leak ++ [leak_c]);
    (* Erased call to unspill *)
    leak <- (leak ++ [(LeakList [(Leak_int (32 * (2 + 4)))])]);
    oram <- (SBArray196608_1536.set_sub64 oram (32 * (2 + 4)) root_node);
    (leak_c, oram) <@ pushDown (oram);
    leak <- (leak ++ [leak_c]);
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    return ((LeakList leak), pos, oram, ans);
  }
  proc read_write_block_export (pos:BArray512.t, oram:BArray196608.t,
                                ans:BArray32.t, i:W64.t, vals:BArray32.t,
                                wr:W8.t) : JLeakage.leakage * BArray512.t *
                                           BArray196608.t * BArray32.t = {
    var leak:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    leak <- [];
    pos <- pos;
    oram <- oram;
    ans <- ans;
    i <- i;
    vals <- vals;
    wr <- wr;
    (leak_c, pos, oram, ans) <@ read_write_block (pos, oram, ans, i, 
    vals, wr);
    leak <- (leak ++ [leak_c]);
    pos <- pos;
    oram <- oram;
    ans <- ans;
    return ((LeakList leak), pos, oram, ans);
  }
  proc multiQuery (pos:BArray512.t, oram:BArray196608.t,
                   queries:BArray2400.t, ans:BArray800.t) : JLeakage.leakage *
                                                            BArray512.t *
                                                            BArray196608.t *
                                                            BArray800.t = {
    var _b:JLeakage.leakages;
    var leak:JLeakage.leakages;
    var leak_0:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var leak_cond:JLeakage.leakages;
    var q:W64.t;
    var q3:W64.t;
    var t:W64.t;
    var i:W64.t;
    var v:W64.t;
    var a:W64.t;
    leak <- [];
    q <- (W64.of_int 0);
    leak_cond <- [];
    _b <- [];
    leak_cond <-
    (leak_cond ++ [(LeakList [(Leak_bool (q \ult (W64.of_int 100)))])]);
    while ((q \ult (W64.of_int 100))) {
      leak_0 <- [];
      q3 <- q;
      (* Erased call to spill *)
      (* Erased call to spill *)
      q3 <- (q3 * (W64.of_int 3));
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint q3))])]);
      t <- (BArray2400.get64 queries (W64.to_uint q3));
      leak_0 <-
      (leak_0 ++
      [(LeakList [(Leak_int (W64.to_uint (q3 + (W64.of_int 1))))])]);
      i <- (BArray2400.get64 queries (W64.to_uint (q3 + (W64.of_int 1))));
      leak_0 <-
      (leak_0 ++
      [(LeakList [(Leak_int (W64.to_uint (q3 + (W64.of_int 2))))])]);
      v <- (BArray2400.get64 queries (W64.to_uint (q3 + (W64.of_int 2))));
      (* Erased call to spill *)
      (leak_c, pos, oram, a) <@ read_write (pos, oram, i, v, (truncateu8 t));
      leak_0 <- (leak_0 ++ [leak_c]);
      (* Erased call to unspill *)
      (* Erased call to unspill *)
      (* Erased call to unspill *)
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint q))])]);
      ans <- (BArray800.set64 ans (W64.to_uint q) a);
      q <- (q + (W64.of_int 1));
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <-
      (leak_cond ++ [(LeakList [(Leak_bool (q \ult (W64.of_int 100)))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    return ((LeakList leak), pos, oram, ans);
  }
  proc multiQuery_export (pos:BArray512.t, oram:BArray196608.t,
                          ans:BArray800.t, queries:BArray2400.t) : JLeakage.leakage *
                                                                   BArray512.t *
                                                                   BArray196608.t *
                                                                   BArray800.t = {
    var leak:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    leak <- [];
    pos <- pos;
    oram <- oram;
    ans <- ans;
    queries <- queries;
    (leak_c, pos, oram, ans) <@ multiQuery (pos, oram, queries, ans);
    leak <- (leak ++ [leak_c]);
    pos <- pos;
    oram <- oram;
    ans <- ans;
    return ((LeakList leak), pos, oram, ans);
  }
  proc multiQuery_blocks (pos:BArray512.t, oram:BArray196608.t,
                          queries:BArray4800.t, ans:BArray3200.t) : JLeakage.leakage *
                                                                    BArray512.t *
                                                                    BArray196608.t *
                                                                    BArray3200.t = {
    var _b:JLeakage.leakages;
    var leak:JLeakage.leakages;
    var leak_0:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    var leak_cond:JLeakage.leakages;
    var q:W64.t;
    var q2b_sz:W64.t;
    var t:W64.t;
    var i:W64.t;
    var vals:BArray32.t;
    var qb_sz:W64.t;
    var this_ans:BArray32.t;
    this_ans <- witness;
    vals <- witness;
    leak <- [];
    q <- (W64.of_int 0);
    leak_cond <- [];
    _b <- [];
    leak_cond <-
    (leak_cond ++ [(LeakList [(Leak_bool (q \ult (W64.of_int 100)))])]);
    while ((q \ult (W64.of_int 100))) {
      leak_0 <- [];
      q2b_sz <- q;
      (* Erased call to spill *)
      (* Erased call to spill *)
      q2b_sz <- (q2b_sz * (W64.of_int ((1 + 1) + 4)));
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint q2b_sz))])]);
      t <- (BArray4800.get64 queries (W64.to_uint q2b_sz));
      leak_0 <-
      (leak_0 ++
      [(LeakList [(Leak_int (W64.to_uint (q2b_sz + (W64.of_int 1))))])]);
      i <-
      (BArray4800.get64 queries (W64.to_uint (q2b_sz + (W64.of_int 1))));
      leak_0 <-
      (leak_0 ++
      [(LeakList [(Leak_int (W64.to_uint (q2b_sz + (W64.of_int 2))))])]);
      vals <-
      (SBArray4800_32.get_sub64 queries
      (W64.to_uint (q2b_sz + (W64.of_int 2))));
      qb_sz <- q;
      qb_sz <- (qb_sz * (W64.of_int 4));
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint qb_sz))])]);
      this_ans <- (SBArray3200_32.get_sub64 ans (W64.to_uint qb_sz));
      (* Erased call to spill *)
      (* Erased call to spill *)
      (leak_c, pos, oram, this_ans) <@ read_write_block (pos, oram, this_ans,
      i, vals, (truncateu8 t));
      leak_0 <- (leak_0 ++ [leak_c]);
      (* Erased call to unspill *)
      (* Erased call to unspill *)
      (* Erased call to unspill *)
      (* Erased call to unspill *)
      leak_0 <- (leak_0 ++ [(LeakList [(Leak_int (W64.to_uint qb_sz))])]);
      ans <- (SBArray3200_32.set_sub64 ans (W64.to_uint qb_sz) this_ans);
      q <- (q + (W64.of_int 1));
      _b <- (_b ++ [(LeakList leak_0)]);
      leak_cond <-
      (leak_cond ++ [(LeakList [(Leak_bool (q \ult (W64.of_int 100)))])]);
    }
    leak <- (leak ++ [(LeakList [(LeakList leak_cond); (LeakList _b)])]);
    return ((LeakList leak), pos, oram, ans);
  }
  proc multiQuery_blocks_export (pos:BArray512.t, oram:BArray196608.t,
                                 ans:BArray3200.t, queries:BArray4800.t) : 
  JLeakage.leakage * BArray512.t * BArray196608.t * BArray3200.t = {
    var leak:JLeakage.leakages;
    var leak_c:JLeakage.leakage;
    leak <- [];
    pos <- pos;
    oram <- oram;
    queries <- queries;
    ans <- ans;
    (leak_c, pos, oram, ans) <@ multiQuery_blocks (pos, oram, queries, ans);
    leak <- (leak ++ [leak_c]);
    pos <- pos;
    oram <- oram;
    ans <- ans;
    return ((LeakList leak), pos, oram, ans);
  }
}.
