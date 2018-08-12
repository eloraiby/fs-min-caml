module Id
type T = string (* �ѿ��̾�� (caml2html: id_t) *)
type L = L of string (* �ȥåץ�٥�ؿ�䥰���Х�����Υ�٥� (caml2html: id_l) *)

let rec ppList = function
  | [] -> ""
  | [x] -> x
  | x :: xs -> x + " " + ppList xs

let counter = ref 0
let genid s =
  incr counter;
  sprintf "%s.%d" s !counter

let rec idOfTyp = function
  | Ty.Unit -> "u"
  | Ty.Bool -> "b"
  | Ty.Int -> "i"
  | Ty.Float -> "d"
  | Ty.Fun _ -> "f"
  | Ty.Tuple _ -> "t"
  | Ty.Array _ -> "a" 
  | Ty.Var _ -> failwith "invalid type id"

let gentmp typ =
  incr counter;
  sprintf "T%s%d" (idOfTyp typ) !counter
