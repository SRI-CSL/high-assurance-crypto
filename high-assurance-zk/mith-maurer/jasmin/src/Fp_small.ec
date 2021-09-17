require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.




module M = {
  proc addm (p:W64.t, a:W64.t, b:W64.t) : W64.t = {
    
    var x:W64.t;
    var k1:W64.t;
    var k2:W64.t;
    var _cf:bool;
    
    k1 <- (W64.of_int 0);
    k2 <- (W64.of_int 0);
    (_cf, x) <- addc_64 a b false;
    k1 <- (_cf ? p : k1);
    (_cf, x) <- subc_64 x p false;
    k2 <- (_cf ? p : k2);
    x <- (x + k2);
    x <- (x - k1);
    return (x);
  }
  
  proc subm (p:W64.t, a:W64.t, b:W64.t) : W64.t = {
    
    var x:W64.t;
    var k:W64.t;
    var _cf:bool;
    
    k <- (W64.of_int 0);
    (_cf, x) <- subc_64 a b false;
    k <- (_cf ? p : k);
    x <- (x + k);
    return (x);
  }
  
  proc mulm (p:W64.t, a:W64.t, b:W64.t) : W64.t = {
    
    var x:W64.t;
    var ax:W64.t;
    var bx:W64.t;
    var mh:W64.t;
    var ml:W64.t;
    var q:W64.t;
    var r:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    
    ax <- a;
    bx <- b;
    ( _0,  _1,  _2,  _3,  _4, mh, ml) <- MUL_64 ax bx;
    ( _5,  _6,  _7,  _8,  _9, q, r) <- DIV_64 mh ml p;
    x <- r;
    return (x);
  }
  
  proc toEC () : unit = {
    
    var p:W64.t;
    var a:W64.t;
    var b:W64.t;
    var r:W64.t;
    
    r <@ addm (p, a, b);
    r <@ subm (p, a, b);
    r <@ mulm (p, a, b);
    return ();
  }
}.

