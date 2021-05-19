open PrimeField
open Lint
   
type group = Z.t

let p = ref Z.zero (*Z.of_string "0x00f9ddcd72a0cc7f4a903d93d26142e23160b4e8ceeab6514f84bd18a722ec01ae4ceb19853e83ac76696ebe338d2981c98a4ca6df127bf80f05a2bbec0a9cafd42e02b4de5f4751ab1e29c036d4b2aeacaec681bd875b86c77d373a1de08a9de9967c8faaf5fdb23ab4dd8c626ae5a58b5f1a65f5167c9d3ff54d8af45e7d56939cfbd79b0b3cdc84f1ca64886fc144cdf6abe1b64870e558d704dbae19c5245ec2162f019cf71b13c9a9e171be862e3e68ad9e5c05ea43f9ff7627e00b2d1db3d3d8fd3b1249dc1493a736e9ac0fddc34d24648e2bb05630a6b0b3967aa38e20317fba29c500646c8a6ab9282993d54ee75d50de7e43dca166b06979c795166a8e6bbd928f61a261ce17c12bea29ac7ff6d63a94818594e116a9377b046123d7689a39773d58e728f65c3c4ef3d10add064f86f27c5b95b77baf60f2f3e2fca3d6a5260d7b421aa133a733ecae42d57adaf3c343f4edfbdbfd6ee78bad00c0242ac814d1c1f301ae8f5cb92d639f7826d54ee1a27fef425aa6f85764de3fb523a34205219dfec1e5b7195df074a2eaadd43c3ab5fb85124369b55aa0769d96e630aaee0bac0f4cfa7ba10c146aa6ef38dbc3bd60189645270d0a3c4708ac96e64e69c52bd3c42a8eb98b6310ac44a36bf6396a1d2bd196c436c6817553df67f128ea4f525a08528e0979970cac16f7cfcae1b8c6a162681b9bfaca945f16233b"*)

let g = ref Z.zero (* Z.of_string "2"*)
              
let cgmul : group -> group -> group = fun a b -> mul_mod a b !p
let cgdiv : group -> group -> group = fun a b -> div_mod a b !p
let cgexp : group -> t -> group = fun a e -> exp_mod a e !p
