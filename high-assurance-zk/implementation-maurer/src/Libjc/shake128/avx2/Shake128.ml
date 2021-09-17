open Batteries
open Shake128Wrapper
                                                                    
let shake128_wrapper (x : string) : string = shake128 x (String.length x)
                                                      (*Format.printf "message = %s\nsize = %d\n\n@." x (String.length x);*)
                                                      (*Format.printf "I received this from C: %s\n" s ;*)
                                                      (*Format.printf "HASH = %s\n@." s ;*)
                                               
