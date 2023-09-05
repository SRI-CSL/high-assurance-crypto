require import AllCore IntDiv CoreMap List.
from Jasmin require import JModel.




module M = {
  proc addm (a:W64.t, b:W64.t) : W64.t = {
    
    
    
    a <- (a `^` b);
    return (a);
  }
  
  proc subm (a:W64.t, b:W64.t) : W64.t = {
    
    
    
    a <- (a `^` b);
    return (a);
  }
  
  proc mulm (a:W64.t, b:W64.t) : W64.t = {
    
    
    
    a <- (a `&` b);
    return (a);
  }
  
  proc toEC () : unit = {
    
    var a:W64.t;
    var b:W64.t;
    var r:W64.t;
    
    r <@ addm (a, b);
    r <@ subm (a, b);
    r <@ mulm (a, b);
    return ();
  }
}.

