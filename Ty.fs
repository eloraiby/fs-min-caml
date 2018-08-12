module Ty
type T = (* MinCaml�η���ɽ������ǡ����� (caml2html: type_t) *)
  | Unit
  | Bool
  | Int
  | Float
  | Fun of T list * T (* arguments are uncurried *)
  | Tuple of T list
  | Array of T
  | Var of Ref<Option<T>> // option ref

let gentyp () = Var(ref None) (* ���������ѿ���� *)
