open Lint

type t = Z.t

let q = ref (Z.of_string "101") ;;

(*ref (Z.of_string "93139822912306381236365199869088867521235099006980001661998968455136786901089");;*)

(*(Z.of_string "176720559783218918034063734871356290855142631469907316943963362457081966166423164635950037023560976338281160564975640194756359253727872734153279226662388512877638981443374374828998827907045853236342402091396191842667512802827724844077795643997662700664479181463563386285525960670664115854574208619448810452653");;*) (*Z.of_string "97"*) (*Z.of_string "1041947277516545182461542431352603523649755409166642159414964802181256267776436198848488809852964437515131621106165443998211354181516192565130728715360424951310047012435498404517638012928424367394086452695902788232422474973036294007713175594327800731626216094409715936622374774677435185603153844482696265228355091281592611425870917621464413441453095456542624381786405113008183927715146170930825157119404770775432850740080624975098055813196489663337469968726632704105549647484546747699864378933819858189036145751512130471471502957118148560709501548481038028031869671597635172857896457205834687771570291049517644433787418359123006571259325577925627640164732816570343715283068632106993925344253428767518330061125256940366604272189861201307159248819823150230938042555716794723676619808751824834396392953957169805761572729454036518768718511255652632497724631317066391858274430904541230565269335495497820009155757304523157900573900149457228331885282155492004449895315073000013585398747459651423450496304247098522646766933538100896061173507695454368029732241895478593064774560165081021828845627801926159395809246077105130781169306302015506241199674466295344317313421706405137883012224942469175554587886841446316187449948231584121972548696359"*)

let zero : t = Z.zero
let one : t = Z.one

let fadd : t -> t -> t = fun a b -> add_mod a b !q
let fumin : t -> t = fun a -> umin_mod a !q
let fsub : t -> t -> t = fun a b -> sub_mod a b !q
let fmul : t -> t -> t = fun a b -> mul_mod a b !q
let fdiv : t -> t -> t = fun a b -> div_mod a b !q
let fexp : t -> t -> t = fun a e -> exp_mod a e !q

let dt : unit -> Z.t = fun _ -> Z.rem (Z.of_bits (Cryptokit.Random.string Cryptokit.Random.secure_rng 128)) !q
