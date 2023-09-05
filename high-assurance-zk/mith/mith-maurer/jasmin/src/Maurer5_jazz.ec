require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.

require import Array4 Array8 Array24.
require import WArray32 WArray64 WArray192.



module M = {
  proc bn2_unpack (a:W64.t Array8.t) : W64.t Array4.t * W64.t Array4.t = {
    var aux: int;
    
    var hi:W64.t Array4.t;
    var lo:W64.t Array4.t;
    var i:int;
    hi <- witness;
    lo <- witness;
    i <- 0;
    while (i < 4) {
      lo.[i] <- a.[i];
      hi.[i] <- a.[(4 + i)];
      i <- i + 1;
    }
    return (hi, lo);
  }
  
  proc bn_eq (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t = {
    var aux: int;
    
    var res_0:W64.t;
    var are_equal:W64.t;
    var acc:W64.t;
    var i:int;
    var t:W64.t;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    res_0 <- (W64.of_int 0);
    are_equal <- (W64.of_int 1);
    acc <- (W64.of_int 0);
    i <- 0;
    while (i < 4) {
      t <- a.[i];
      t <- (t `^` b.[i]);
      acc <- (acc `|` t);
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 acc acc;
    res_0 <- (zf ? are_equal : res_0);
    return (res_0);
  }
  
  proc bn_test0 (a:W64.t Array4.t) : W64.t = {
    var aux: int;
    
    var res_0:W64.t;
    var is_zero:W64.t;
    var acc:W64.t;
    var i:int;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    
    res_0 <- (W64.of_int 0);
    is_zero <- (W64.of_int 1);
    acc <- a.[0];
    i <- 1;
    while (i < 4) {
      acc <- (acc `|` a.[i]);
      i <- i + 1;
    }
    ( _0,  _1,  _2,  _3, zf,  _4) <- AND_64 acc acc;
    res_0 <- (zf ? is_zero : res_0);
    return (res_0);
  }
  
  proc bn_add1 (a:W64.t Array4.t, b:W64.t) : bool * W64.t Array4.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    (aux, aux_0) <- addc_64 a.[0] b false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < 4) {
      (aux, aux_0) <- addc_64 a.[i] (W64.of_int 0) cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_addc (a:W64.t Array4.t, b:W64.t Array4.t) : bool * W64.t Array4.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    (aux, aux_0) <- addc_64 a.[0] b.[0] false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < 4) {
      (aux, aux_0) <- addc_64 a.[i] b.[i] cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_subc (a:W64.t Array4.t, b:W64.t Array4.t) : bool * W64.t Array4.t = {
    var aux: bool;
    var aux_1: int;
    var aux_0: W64.t;
    
    var cf:bool;
    var i:int;
    
    (aux, aux_0) <- subc_64 a.[0] b.[0] false;
    cf <- aux;
    a.[0] <- aux_0;
    i <- 1;
    while (i < 4) {
      (aux, aux_0) <- subc_64 a.[i] b.[i] cf;
      cf <- aux;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc mul1 (a:W64.t, b:W64.t Array4.t) : W64.t * bool * bool *
                                          W64.t Array8.t = {
    var aux_2: bool;
    var aux_1: int;
    var aux_0: W64.t;
    var aux: W64.t;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array8.t;
    var i:int;
    var lo:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    r <- witness;
    (of_0, cf,  _0,  _1,  _2, _zero) <- set0_64 ;
    (aux_0, aux) <- MULX_64 a b.[0];
    r.[1] <- aux_0;
    r.[0] <- aux;
    i <- 1;
    while (i < 4) {
      (aux_0, aux) <- MULX_64 a b.[i];
      r.[(i + 1)] <- aux_0;
      lo <- aux;
      (aux_2, aux_0) <- ADCX_64 r.[i] lo cf;
      cf <- aux_2;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    (aux_2, aux_0) <- ADCX_64 r.[4] _zero cf;
    cf <- aux_2;
    r.[4] <- aux_0;
    return (_zero, of_0, cf, r);
  }
  
  proc mul1acc (k:int, a:W64.t, b:W64.t Array4.t, r:W64.t Array8.t,
                _zero:W64.t, of_0:bool, cf:bool) : W64.t * bool * bool *
                                                   W64.t Array8.t = {
    var aux_0: bool;
    var aux: int;
    var aux_2: W64.t;
    var aux_1: W64.t;
    
    var i:int;
    var hi:W64.t;
    var lo:W64.t;
    
    aux <- (4 - 1);
    i <- 0;
    while (i < aux) {
      (hi, lo) <- MULX_64 a b.[i];
      (aux_0, aux_2) <- ADOX_64 r.[(k + i)] lo of_0;
      of_0 <- aux_0;
      r.[(k + i)] <- aux_2;
      (aux_0, aux_2) <- ADCX_64 r.[((k + i) + 1)] hi cf;
      cf <- aux_0;
      r.[((k + i) + 1)] <- aux_2;
      i <- i + 1;
    }
    (aux_2, aux_1) <- MULX_64 a b.[(4 - 1)];
    r.[(4 + k)] <- aux_2;
    lo <- aux_1;
    (aux_0, aux_2) <- ADOX_64 r.[((4 + k) - 1)] lo of_0;
    of_0 <- aux_0;
    r.[((4 + k) - 1)] <- aux_2;
    (aux_0, aux_2) <- ADCX_64 r.[(4 + k)] _zero cf;
    cf <- aux_0;
    r.[(4 + k)] <- aux_2;
    (aux_0, aux_2) <- ADOX_64 r.[(4 + k)] _zero of_0;
    of_0 <- aux_0;
    r.[(4 + k)] <- aux_2;
    return (_zero, of_0, cf, r);
  }
  
  proc bn_muln (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t * bool * bool *
                                                      W64.t Array8.t = {
    var aux: int;
    
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var r:W64.t Array8.t;
    var ai:W64.t;
    var i:int;
    r <- witness;
    ai <- a.[0];
    (_zero, of_0, cf, r) <@ mul1 (ai, b);
    i <- 1;
    while (i < 4) {
      ai <- a.[i];
      (_zero, of_0, cf, r) <@ mul1acc (i, ai, b, r, _zero, of_0, cf);
      i <- i + 1;
    }
    return (_zero, of_0, cf, r);
  }
  
  proc maskOnCarry (mask:int, r:W64.t, _cf:bool) : W64.t = {
    
    
    
    (_cf, r) <- subc_64 r r _cf;
    r <- (r `&` (W64.of_int mask));
    return (r);
  }
  
  proc x2r (x0:W64.t, x1:W64.t, x2:W64.t, x3:W64.t) : W64.t Array4.t = {
    
    var r:W64.t Array4.t;
    r <- witness;
    r.[0] <- x0;
    r.[1] <- x1;
    r.[2] <- x2;
    r.[3] <- x3;
    return (r);
  }
  
  proc r2x (x:W64.t Array4.t) : W64.t * W64.t * W64.t * W64.t = {
    
    var r0:W64.t;
    var r1:W64.t;
    var r2:W64.t;
    var r3:W64.t;
    
    r0 <- x.[0];
    r1 <- x.[1];
    r2 <- x.[2];
    r3 <- x.[3];
    return (r0, r1, r2, r3);
  }
  
  proc cminusP (x:W64.t Array4.t) : W64.t Array4.t = {
    var aux: bool;
    var aux_0: W64.t;
    
    var t:W64.t Array4.t;
    var twop63:W64.t;
    var cf:bool;
    t <- witness;
    t <- x;
    twop63 <- (W64.of_int 1);
    twop63 <- (twop63 `<<` (W8.of_int 63));
    (aux, aux_0) <- addc_64 t.[0] (W64.of_int 19) false;
    cf <- aux;
    t.[0] <- aux_0;
    (aux, aux_0) <- addc_64 t.[1] (W64.of_int 0) cf;
    cf <- aux;
    t.[1] <- aux_0;
    (aux, aux_0) <- addc_64 t.[2] (W64.of_int 0) cf;
    cf <- aux;
    t.[2] <- aux_0;
    (aux, aux_0) <- addc_64 t.[3] twop63 cf;
    cf <- aux;
    t.[3] <- aux_0;
    x.[0] <- (cf ? t.[0] : x.[0]);
    x.[1] <- (cf ? t.[1] : x.[1]);
    x.[2] <- (cf ? t.[2] : x.[2]);
    x.[3] <- (cf ? t.[3] : x.[3]);
    return (x);
  }
  
  proc caddP (cf:bool, x:W64.t Array4.t) : W64.t Array4.t = {
    
    var p:W64.t Array4.t;
    var _zero:W64.t;
    var  _0:bool;
    p <- witness;
    p.[0] <- (W64.of_int 18446744073709551597);
    p.[1] <- (W64.of_int 18446744073709551615);
    p.[2] <- (W64.of_int 18446744073709551615);
    p.[3] <- (W64.of_int 9223372036854775807);
    _zero <- (W64.of_int 0);
    p.[0] <- ((! cf) ? _zero : p.[0]);
    p.[1] <- ((! cf) ? _zero : p.[1]);
    p.[2] <- ((! cf) ? _zero : p.[2]);
    p.[3] <- ((! cf) ? _zero : p.[3]);
    ( _0, x) <@ bn_addc (x, p);
    return (x);
  }
  
  proc redp25519 (_of:bool, _cf:bool, a:W64.t Array8.t) : W64.t Array4.t = {
    
    var al:W64.t Array4.t;
    var tmp:W64.t;
    var _zero:W64.t;
    var ah:W64.t Array4.t;
    var  _0:W64.t Array4.t;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:W64.t Array4.t;
     _0 <- witness;
     _6 <- witness;
    ah <- witness;
    al <- witness;
    tmp <- (W64.of_int 38);
    _zero <- (W64.of_int 0);
    (ah,  _0) <@ bn2_unpack (a);
    (_zero, _of, _cf, a) <@ mul1acc (0, tmp, ah, a, _zero, _of, _cf);
    ( _1,  _2,  _3,  _4,  _5, tmp) <- IMULri_64 a.[4] (W64.of_int 38);
    ( _6, al) <@ bn2_unpack (a);
    (_cf, al) <@ bn_add1 (al, tmp);
    tmp <@ maskOnCarry (38, tmp, _cf);
    al.[0] <- (al.[0] + tmp);
    return (al);
  }
  
  proc freeze (x:W64.t Array4.t) : W64.t Array4.t = {
    
    
    
    x <@ cminusP (x);
    x <@ cminusP (x);
    return (x);
  }
  
  proc _mulm (f:W64.t Array4.t, g0:W64.t, g1:W64.t, g2:W64.t, g3:W64.t) : 
  W64.t * W64.t * W64.t * W64.t = {
    
    var g:W64.t Array4.t;
    var _zero:W64.t;
    var of_0:bool;
    var cf:bool;
    var h:W64.t Array8.t;
    g <- witness;
    h <- witness;
    g <@ x2r (g0, g1, g2, g3);
    (_zero, of_0, cf, h) <@ bn_muln (f, g);
    g <@ redp25519 (of_0, cf, h);
    g <@ freeze (g);
    (g0, g1, g2, g3) <@ r2x (g);
    return (g0, g1, g2, g3);
  }
  
  proc mulm (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t Array4.t = {
    
    var g0:W64.t;
    var g1:W64.t;
    var g2:W64.t;
    var g3:W64.t;
    
    (g0, g1, g2, g3) <@ r2x (b);
    (g0, g1, g2, g3) <@ _mulm (a, g0, g1, g2, g3);
    b <@ x2r (g0, g1, g2, g3);
    return (b);
  }
  
  proc _addm (f0:W64.t, f1:W64.t, f2:W64.t, f3:W64.t, g0:W64.t, g1:W64.t,
              g2:W64.t, g3:W64.t) : W64.t * W64.t * W64.t * W64.t = {
    
    var f:W64.t Array4.t;
    var g:W64.t Array4.t;
    var  _0:bool;
    f <- witness;
    g <- witness;
    f <@ x2r (f0, f1, f2, f3);
    g <@ x2r (g0, g1, g2, g3);
    ( _0, f) <@ bn_addc (f, g);
    f <@ cminusP (f);
    (f0, f1, f2, f3) <@ r2x (f);
    return (f0, f1, f2, f3);
  }
  
  proc addm (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t Array4.t = {
    
    var f0:W64.t;
    var f1:W64.t;
    var f2:W64.t;
    var f3:W64.t;
    var g0:W64.t;
    var g1:W64.t;
    var g2:W64.t;
    var g3:W64.t;
    
    (f0, f1, f2, f3) <@ r2x (a);
    (g0, g1, g2, g3) <@ r2x (b);
    (f0, f1, f2, f3) <@ _addm (f0, f1, f2, f3, g0, g1, g2, g3);
    a <@ x2r (f0, f1, f2, f3);
    return (a);
  }
  
  proc _subm (f0:W64.t, f1:W64.t, f2:W64.t, f3:W64.t, g0:W64.t, g1:W64.t,
              g2:W64.t, g3:W64.t) : W64.t * W64.t * W64.t * W64.t = {
    
    var f:W64.t Array4.t;
    var g:W64.t Array4.t;
    var cf:bool;
    f <- witness;
    g <- witness;
    f <@ x2r (f0, f1, f2, f3);
    g <@ x2r (g0, g1, g2, g3);
    (cf, f) <@ bn_subc (f, g);
    f <@ caddP (cf, f);
    (f0, f1, f2, f3) <@ r2x (f);
    return (f0, f1, f2, f3);
  }
  
  proc subm (a:W64.t Array4.t, b:W64.t Array4.t) : W64.t Array4.t = {
    
    var f0:W64.t;
    var f1:W64.t;
    var f2:W64.t;
    var f3:W64.t;
    var g0:W64.t;
    var g1:W64.t;
    var g2:W64.t;
    var g3:W64.t;
    
    (f0, f1, f2, f3) <@ r2x (a);
    (g0, g1, g2, g3) <@ r2x (b);
    (f0, f1, f2, f3) <@ _subm (f0, f1, f2, f3, g0, g1, g2, g3);
    a <@ x2r (f0, f1, f2, f3);
    return (a);
  }
  
  proc load_array (in_0:W64.t) : W64.t Array4.t = {
    var aux: int;
    
    var out:W64.t Array4.t;
    var i:int;
    out <- witness;
    i <- 0;
    while (i < 4) {
      out.[i] <-
      (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int (i * 8)))));
      i <- i + 1;
    }
    return (out);
  }
  
  proc load_array_st (in_0:W64.t) : W64.t Array4.t = {
    var aux: int;
    
    var out:W64.t Array4.t;
    var i:int;
    out <- witness;
    i <- 0;
    while (i < 4) {
      out.[i] <-
      (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int (i * 8)))));
      i <- i + 1;
    }
    return (out);
  }
  
  proc store_array (out:W64.t, in_0:W64.t Array4.t) : unit = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 4) {
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (i * 8)))) in_0.[i];
      i <- i + 1;
    }
    return ();
  }
  
  proc add_wrapper (v1S:W64.t, v2S:W64.t, resS:W64.t) : unit = {
    
    var v1:W64.t;
    var f:W64.t Array4.t;
    var v2:W64.t;
    var g:W64.t Array4.t;
    var r:W64.t Array4.t;
    var vR:W64.t;
    f <- witness;
    g <- witness;
    r <- witness;
    v1 <- v1S;
    f <@ load_array (v1);
    v2 <- v2S;
    g <@ load_array (v2);
    r <@ addm (f, g);
    vR <- resS;
    store_array (vR, r);
    return ();
  }
  
  proc mult_wrapper (v1S:W64.t, v2S:W64.t, resS:W64.t) : unit = {
    
    var v1:W64.t;
    var f:W64.t Array4.t;
    var v2:W64.t;
    var g:W64.t Array4.t;
    var vR:W64.t;
    var r:W64.t Array4.t;
    f <- witness;
    g <- witness;
    r <- witness;
    v1 <- v1S;
    f <@ load_array_st (v1);
    v2 <- v2S;
    g <@ load_array (v2);
    vR <- resS;
    r <@ mulm (f, g);
    vR <- resS;
    store_array (vR, r);
    return ();
  }
  
  proc sub_wrapper (v1S:W64.t, v2S:W64.t, resS:W64.t) : unit = {
    
    var v1:W64.t;
    var f:W64.t Array4.t;
    var v2:W64.t;
    var g:W64.t Array4.t;
    var r:W64.t Array4.t;
    var vR:W64.t;
    f <- witness;
    g <- witness;
    r <- witness;
    v1 <- v1S;
    f <@ load_array (v1);
    v2 <- v2S;
    g <@ load_array (v2);
    r <@ subm (f, g);
    vR <- resS;
    store_array (vR, r);
    return ();
  }
  
  proc getWireIndex5 (wi:W64.t) : W64.t = {
    
    var res_0:W64.t;
    
    res_0 <- (wi * (W64.of_int 6));
    res_0 <- (res_0 * (W64.of_int 4));
    res_0 <- (res_0 * (W64.of_int 8));
    return (res_0);
  }
  
  proc getShareIndex (si:int) : int = {
    
    var res_0:int;
    
    res_0 <- (si * 4);
    res_0 <- (res_0 * 8);
    return (res_0);
  }
  
  proc getMessageIndex (wi:int) : int = {
    
    var res_0:int;
    
    res_0 <- (wi * 6);
    res_0 <- (res_0 * 4);
    res_0 <- (res_0 * 8);
    return (res_0);
  }
  
  proc copy_share (out:W64.t, in_0:W64.t) : unit = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 4) {
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (i * 8)))) (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int (i * 8)))));
      i <- i + 1;
    }
    return ();
  }
  
  proc copy_message (out:W64.t, in_0:W64.t) : unit = {
    var aux: int;
    
    var i:int;
    
    aux <- (6 * 4);
    i <- 0;
    while (i < aux) {
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (i * 8)))) (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int (i * 8)))));
      i <- i + 1;
    }
    return ();
  }
  
  proc set0 (out:W64.t) : unit = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 4) {
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (i * 8)))) (W64.of_int 0);
      i <- i + 1;
    }
    return ();
  }
  
  proc create_sharing (outS:W64.t, randomnessS:W64.t) : unit = {
    
    var randomness:W64.t;
    var randomness1:W64.t;
    var out:W64.t;
    var aux2:W64.t;
    var aux1:W64.t;
    
    randomness <- randomnessS;
    randomness1 <- randomness;
    out <- outS;
    aux2 <- (randomness1 + (W64.of_int ((5 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 16)));
    aux2 <- (randomness1 + (W64.of_int ((8 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((7 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((4 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((6 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((1 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((2 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux1 <- outS;
    aux2 <- (aux1 + (W64.of_int (4 * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((3 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((8 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((7 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((6 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((0 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((2 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((5 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux1 <- outS;
    aux2 <- (aux1 + (W64.of_int (4 * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((3 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((3 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((8 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((4 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((6 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((0 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((1 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((7 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((4 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((0 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((1 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((2 * 4) * 8)));
    copy_share (out, aux2);
    randomness1 <- randomness;
    out <- (out + (W64.of_int (4 * 8)));
    aux2 <- (randomness1 + (W64.of_int ((5 * 4) * 8)));
    copy_share (out, aux2);
    return ();
  }
  
  proc create_sharing_const (outS:W64.t, conS:W64.t, minusS:W64.t) : unit = {
    
    var out:W64.t;
    var x:W64.t;
    var minus:W64.t;
    
    out <- outS;
    x <- conS;
    minus <- minusS;
    out <- outS;
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    set0 (out);
    out <- (out + (W64.of_int (4 * 8)));
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    set0 (out);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    set0 (out);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, minus);
    out <- (out + (W64.of_int (4 * 8)));
    copy_share (out, x);
    return ();
  }
  
  proc add5 (status:W64.t, w1:W64.t, w2:W64.t, curwire:W64.t) : W64.t = {
    var aux_0: int;
    
    var aux:W64.t;
    var wi:W64.t;
    var st:W64.t;
    var w1S:W64.t;
    var w2S:W64.t;
    var wresS:W64.t;
    var shareN:int;
    var i:int;
    var sw1:W64.t;
    var sw2:W64.t;
    var swres:W64.t;
    var xi:W64.t;
    var yi:W64.t;
    var resi:W64.t;
    var aux2:W64.t;
    var aux3:W64.t;
    var val1:W64.t;
    var val2:W64.t;
    var resval:W64.t;
    
    wi <- curwire;
    st <- status;
    w1S <- w1;
    w2S <- w2;
    wresS <- wi;
    shareN <- 0;
    while (shareN < 6) {
      i <- (shareN * 4);
      sw1 <- w1S;
      sw2 <- w2S;
      swres <- wresS;
      xi <- (sw1 * (W64.of_int 6));
      xi <- (xi * (W64.of_int 4));
      xi <- (xi + (W64.of_int i));
      yi <- (sw2 * (W64.of_int 6));
      yi <- (yi * (W64.of_int 4));
      yi <- (yi + (W64.of_int i));
      resi <- (swres * (W64.of_int 6));
      resi <- (resi * (W64.of_int 4));
      resi <- (resi + (W64.of_int i));
      aux <- (xi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      val1 <- aux3;
      aux <- (yi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      val2 <- aux3;
      aux <- (resi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      resval <- aux3;
      add_wrapper (val1, val2, resval);
      shareN <- shareN + 1;
    }
    aux <- wresS;
    aux <- (aux + (W64.of_int 1));
    return (aux);
  }
  
  proc createLastShare (randoms:W64.t, out2:W64.t, secret:W64.t) : unit = {
    var aux: int;
    
    var rd3:W64.t;
    var rd2:W64.t;
    var secretS:W64.t;
    var i:int;
    var si:int;
    var aux1:W64.t;
    var x:W64.t;
    var y:W64.t;
    
    rd3 <- randoms;
    rd2 <- out2;
    secretS <- secret;
    copy_share (rd2, rd3);
    aux <- (10 - 1);
    i <- 1;
    while (i < aux) {
      si <@ getShareIndex (i);
      rd3 <- randoms;
      aux1 <- (rd3 + (W64.of_int si));
      x <- aux1;
      y <- out2;
      add_wrapper (x, y, y);
      i <- i + 1;
    }
    sub_wrapper (secretS, y, y);
    return ();
  }
  
  proc input_start5 (input:W64.t, out:W64.t, randomness:W64.t) : unit = {
    
    var outS:W64.t;
    var n:int;
    var rd:W64.t;
    var outS2:W64.t;
    var randomnessS:W64.t;
    var secret:W64.t;
    
    outS <- out;
    n <- (4 * 8);
    rd <- (out + (W64.of_int n));
    outS2 <- rd;
    rd <- randomness;
    randomnessS <- rd;
    secret <- input;
    createLastShare (randomnessS, outS2, secret);
    create_sharing (outS, randomnessS);
    return ();
  }
  
  proc input_end5 (all_messages:W64.t, status:W64.t, curwire:W64.t) : 
  W64.t = {
    
    var wi:W64.t;
    var index:W64.t;
    var st:W64.t;
    var wire:W64.t;
    
    wi <- curwire;
    index <@ getWireIndex5 (wi);
    st <- status;
    wire <- (st + index);
    copy_message (wire, all_messages);
    wi <- (wi + (W64.of_int 1));
    return (wi);
  }
  
  proc const_start5 (input:W64.t, out:W64.t) : unit = {
    
    var conS:W64.t;
    var outS:W64.t;
    var i:int;
    var minus:W64.t;
    var minusS:W64.t;
    
    conS <- input;
    outS <- out;
    set0 (out);
    i <- ((2 * 4) * 8);
    minus <- (out + (W64.of_int i));
    minusS <- minus;
    sub_wrapper (outS, conS, minusS);
    create_sharing_const (outS, conS, minusS);
    return ();
  }
  
  proc const_end5 (message:W64.t, status:W64.t, curwire:W64.t) : W64.t = {
    
    var wi:W64.t;
    var index:W64.t;
    var st:W64.t;
    var wire:W64.t;
    
    wi <- curwire;
    index <@ getWireIndex5 (wi);
    st <- status;
    wire <- (st + index);
    copy_message (wire, message);
    wi <- (wi + (W64.of_int 1));
    return (wi);
  }
  
  proc smult5 (status:W64.t, w1:W64.t, wcons:W64.t, curwire:W64.t) : 
  W64.t = {
    var aux_0: int;
    
    var aux:W64.t;
    var wi:W64.t;
    var st:W64.t;
    var w1S:W64.t;
    var wresS:W64.t;
    var sw1:W64.t;
    var xi:W64.t;
    var aux2:W64.t;
    var aux3:W64.t;
    var val2:W64.t;
    var shareN:int;
    var i:int;
    var swres:W64.t;
    var resi:W64.t;
    var val1:W64.t;
    var resval:W64.t;
    
    wi <- curwire;
    st <- status;
    w1S <- w1;
    wresS <- wi;
    sw1 <- wcons;
    xi <- (sw1 * (W64.of_int 6));
    xi <- (xi * (W64.of_int 4));
    aux <- (xi * (W64.of_int 8));
    aux2 <- st;
    aux3 <- (aux2 + aux);
    val2 <- aux3;
    shareN <- 0;
    while (shareN < 6) {
      i <- (shareN * 4);
      sw1 <- w1S;
      swres <- wresS;
      xi <- (sw1 * (W64.of_int 6));
      xi <- (xi * (W64.of_int 4));
      xi <- (xi + (W64.of_int i));
      resi <- (swres * (W64.of_int 6));
      resi <- (resi * (W64.of_int 4));
      resi <- (resi + (W64.of_int i));
      aux <- (xi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      val1 <- aux3;
      aux <- (resi * (W64.of_int 8));
      aux2 <- st;
      aux3 <- (aux2 + aux);
      resval <- aux3;
      mult_wrapper (val1, val2, resval);
      shareN <- shareN + 1;
    }
    aux <- wresS;
    aux <- (aux + (W64.of_int 1));
    return (aux);
  }
  
  proc mult_pair5 (st:W64.t, resvalS:W64.t, sw1:W64.t, sw2:W64.t, share1:int,
                   share2:int) : unit = {
    
    var i1:int;
    var i2:int;
    var sw:W64.t;
    var xi:W64.t;
    var yi:W64.t;
    var aux:W64.t;
    var aux2:W64.t;
    var val1:W64.t;
    var val1S:W64.t;
    var val2:W64.t;
    var val2S:W64.t;
    
    i1 <- (share1 * 4);
    i2 <- (share2 * 4);
    sw <- sw1;
    xi <- (sw * (W64.of_int 6));
    xi <- (xi * (W64.of_int 4));
    xi <- (xi + (W64.of_int i1));
    sw <- sw2;
    yi <- (sw2 * (W64.of_int 6));
    yi <- (yi * (W64.of_int 4));
    yi <- (yi + (W64.of_int i2));
    aux <- (xi * (W64.of_int 8));
    aux2 <- st;
    val1 <- (aux2 + aux);
    val1S <- val1;
    aux <- (yi * (W64.of_int 8));
    aux2 <- st;
    val2 <- (aux2 + aux);
    val2S <- val2;
    mult_wrapper (val1S, val2S, resvalS);
    return ();
  }
  
  proc mult_start5 (status:W64.t, w1:W64.t, w2:W64.t, outI:W64.t,
                    randomnessI:W64.t) : unit = {
    
    var randomness:W64.t;
    var out:W64.t;
    var st:W64.t;
    var sw1:W64.t;
    var sw2:W64.t;
    var nShares:int;
    var n:int;
    var aux1:W64.t;
    var valmult:W64.t;
    
    set0 (outI);
    randomness <- randomnessI;
    out <- outI;
    st <- status;
    sw1 <- w1;
    sw2 <- w2;
    nShares <- (10 - 1);
    n <- (4 * 8);
    aux1 <- (outI + (W64.of_int n));
    valmult <- aux1;
    mult_pair5 (st, valmult, sw1, sw2, 0, 0);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 0, 1);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 0, 2);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 0, 4);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 1, 3);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 1, 4);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 1, 5);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 2, 0);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 2, 2);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 2, 3);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 2, 4);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 3, 0);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 3, 1);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 3, 2);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 3, 5);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 4, 1);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 4, 2);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 4, 3);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 5, 0);
    add_wrapper (valmult, out, out);
    mult_pair5 (st, valmult, sw1, sw2, 5, 3);
    add_wrapper (valmult, out, out);
    aux1 <- out;
    createLastShare (randomness, valmult, aux1);
    create_sharing (out, randomness);
    return ();
  }
  
  proc mult_end5 (all_messages:W64.t, status:W64.t, curwire:W64.t) : 
  W64.t = {
    var aux: int;
    
    var aux1:W64.t;
    var wi:W64.t;
    var wiS:W64.t;
    var index:W64.t;
    var messages:W64.t;
    var st:W64.t;
    var wire:W64.t;
    var message:W64.t;
    var i:int;
    var si:int;
    var val:W64.t;
    var aux2:W64.t;
    var sumShare:W64.t;
    var p:int;
    var mi:int;
    var valS:W64.t;
    var sumShareS:W64.t;
    
    wi <- curwire;
    wiS <- wi;
    index <@ getWireIndex5 (wi);
    messages <- all_messages;
    st <- status;
    aux1 <- (st + index);
    wire <- aux1;
    message <- messages;
    i <- 0;
    while (i < 6) {
      si <- (i * 4);
      si <- (si * 8);
      aux1 <- message;
      val <- (aux1 + (W64.of_int si));
      aux2 <- wire;
      sumShare <- (aux2 + (W64.of_int si));
      copy_share (sumShare, val);
      i <- i + 1;
    }
    p <- 1;
    while (p < 5) {
      mi <- ((p * 6) * 4);
      mi <- (mi * 8);
      aux1 <- messages;
      aux2 <- (aux1 + (W64.of_int mi));
      message <- aux2;
      i <- 0;
      while (i < 6) {
        si <- (i * 4);
        si <- (si * 8);
        aux1 <- message;
        val <- (aux1 + (W64.of_int si));
        valS <- val;
        aux2 <- wire;
        sumShare <- (aux2 + (W64.of_int si));
        sumShareS <- sumShare;
        add_wrapper (valS, sumShareS, sumShareS);
        i <- i + 1;
      }
      p <- p + 1;
    }
    aux1 <- wiS;
    aux1 <- (aux1 + (W64.of_int 1));
    return (aux1);
  }
  
  proc out_start5 (status:W64.t, wout:W64.t, messages:W64.t) : unit = {
    var aux: int;
    
    var st:W64.t;
    var wi:W64.t;
    var wire:W64.t;
    var p:int;
    var mi:int;
    var msgs:W64.t;
    var mAux:W64.t;
    
    st <- status;
    wi <- (wout * (W64.of_int 6));
    wi <- (wi * (W64.of_int 4));
    wi <- (wi * (W64.of_int 8));
    wire <- (st + wi);
    p <- 0;
    while (p < 5) {
      mi <- (p * 6);
      mi <- (mi * 4);
      mi <- (mi * 8);
      msgs <- messages;
      mAux <- (msgs + (W64.of_int mi));
      copy_message (mAux, wire);
      p <- p + 1;
    }
    return ();
  }
  
  proc out_end5 (all_messages:W64.t, out:W64.t, curwire:W64.t) : unit = {
    
    var wi:W64.t;
    var index:W64.t;
    var messages:W64.t;
    var sumShare:W64.t;
    var mi:int;
    var aux1:W64.t;
    var message:W64.t;
    var si:int;
    var aux2:W64.t;
    var val:W64.t;
    
    wi <- curwire;
    index <@ getWireIndex5 (wi);
    messages <- all_messages;
    sumShare <- out;
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (0 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    copy_share (out, aux2);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (1 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (2 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (3 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (4 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((0 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (5 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((1 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (0 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((1 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (1 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((1 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (3 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    mi <- ((2 * 6) * 4);
    mi <- (mi * 8);
    aux1 <- messages;
    message <- (aux1 + (W64.of_int mi));
    si <- (1 * 4);
    si <- (si * 8);
    aux1 <- message;
    aux2 <- (aux1 + (W64.of_int si));
    val <- aux2;
    add_wrapper (val, sumShare, sumShare);
    return ();
  }
  
  proc copy_message_st (out:W64.t, in_0:W64.t Array24.t) : unit = {
    var aux_0: int;
    
    var i:int;
    var aux:W64.t;
    
    aux_0 <- (6 * 4);
    i <- 0;
    while (i < aux_0) {
      aux <- in_0.[i];
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (out + (W64.of_int (i * 8)))) aux;
      i <- i + 1;
    }
    return ();
  }
  
  proc backup_message (in_0:W64.t) : W64.t Array24.t = {
    var aux: int;
    
    var out:W64.t Array24.t;
    var i:int;
    out <- witness;
    aux <- (6 * 4);
    i <- 0;
    while (i < aux) {
      out.[i] <-
      (loadW64 Glob.mem (W64.to_uint (in_0 + (W64.of_int (i * 8)))));
      i <- i + 1;
    }
    return (out);
  }
  
  proc switch_values (message1:W64.t, message2:W64.t) : unit = {
    
    var backup:W64.t Array24.t;
    backup <- witness;
    backup <@ backup_message (message2);
    copy_message (message2, message1);
    copy_message_st (message1, backup);
    return ();
  }
  
  proc dispatch (party0In:W64.t, party1In:W64.t, party2In:W64.t,
                 party3In:W64.t, party4In:W64.t) : unit = {
    
    var party0:W64.t;
    var party1:W64.t;
    var party2:W64.t;
    var party3:W64.t;
    var party4:W64.t;
    var aux:W64.t;
    var si:int;
    var share1:W64.t;
    var share2:W64.t;
    
    party0 <- party0In;
    party1 <- party1In;
    party2 <- party2In;
    party3 <- party3In;
    party4 <- party4In;
    aux <- party0;
    si <@ getMessageIndex (1);
    share1 <- (aux + (W64.of_int si));
    aux <- party1;
    si <@ getMessageIndex (0);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    aux <- party0;
    si <@ getMessageIndex (2);
    share1 <- (aux + (W64.of_int si));
    aux <- party2;
    si <@ getMessageIndex (0);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    aux <- party0;
    si <@ getMessageIndex (3);
    share1 <- (aux + (W64.of_int si));
    aux <- party3;
    si <@ getMessageIndex (0);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    aux <- party0;
    si <@ getMessageIndex (4);
    share1 <- (aux + (W64.of_int si));
    aux <- party4;
    si <@ getMessageIndex (0);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    aux <- party1;
    si <@ getMessageIndex (2);
    share1 <- (aux + (W64.of_int si));
    aux <- party2;
    si <@ getMessageIndex (1);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    aux <- party1;
    si <@ getMessageIndex (3);
    share1 <- (aux + (W64.of_int si));
    aux <- party3;
    si <@ getMessageIndex (1);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    aux <- party1;
    si <@ getMessageIndex (4);
    share1 <- (aux + (W64.of_int si));
    aux <- party4;
    si <@ getMessageIndex (1);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    aux <- party2;
    si <@ getMessageIndex (3);
    share1 <- (aux + (W64.of_int si));
    aux <- party3;
    si <@ getMessageIndex (2);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    aux <- party2;
    si <@ getMessageIndex (4);
    share1 <- (aux + (W64.of_int si));
    aux <- party4;
    si <@ getMessageIndex (2);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    aux <- party3;
    si <@ getMessageIndex (4);
    share1 <- (aux + (W64.of_int si));
    aux <- party4;
    si <@ getMessageIndex (3);
    share2 <- (aux + (W64.of_int si));
    switch_values (share1, share2);
    return ();
  }
  
  proc toEC (a1:W64.t, a2:W64.t, a3:W64.t, a4:W64.t, a5:W64.t) : unit = {
    
    var x1:W64.t Array4.t;
    var x2:W64.t Array4.t;
    var  _0:W64.t;
    var  _1:W64.t;
    var  _2:W64.t;
    var  _3:W64.t;
    var  _4:W64.t;
    var  _5:W64.t;
    var  _6:W64.t;
    x1 <- witness;
    x2 <- witness;
     _0 <@ bn_eq (x1, x2);
     _1 <@ bn_test0 (x1);
     _2 <@ add5 (a1, a2, a3, a4);
     _3 <@ smult5 (a1, a2, a3, a4);
    dispatch (a1, a2, a3, a4, a5);
    input_start5 (a1, a2, a3);
     _4 <@ input_end5 (a1, a2, a3);
    const_start5 (a1, a2);
     _5 <@ const_end5 (a1, a2, a3);
    mult_start5 (a1, a2, a3, a4, a5);
     _6 <@ mult_end5 (a1, a2, a3);
    out_start5 (a1, a2, a3);
    out_end5 (a1, a2, a3);
    return ();
  }
}.

