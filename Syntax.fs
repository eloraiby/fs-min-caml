module Syntax
type T = (* MinCaml�ι�ʸ��ɽ������ǡ����� (caml2html: syntax_t) *)
  | Unit
  | Bool of bool
  | Int of int
  | Float of float
  | Not of T
  | Neg of T
  | Add of T * T
  | Sub of T * T
  | FNeg of T
  | FAdd of T * T
  | FSub of T * T
  | FMul of T * T
  | FDiv of T * T
  | Eq of T * T
  | LE of T * T
  | If of T * T * T
  | Let of (Id.T * Ty.T) * T * T
  | Var of Id.T
  | LetRec of FunDef * T
  | App of T * (T list)
  | Tuple of T list
  | LetTuple of (Id.T * Ty.T) list * T * T
  | Array of T * T
  | Get of T * T
  | Put of T * T * T
and FunDef = { name : Id.T * Ty.T; args : (Id.T * Ty.T) list; body : T }
