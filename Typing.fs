module Typing

(* type inference/reconstruction *)
module Map =
    let addList (xs: ('K * 'V) list) (m: Map<'K, 'V>) =
        xs
        |> List.fold (fun (m: Map<'K, 'V>) (k, v) -> m.Add(k, v)) m

open Syntax

exception Unify of Ty.T * Ty.T
exception Error of T * Ty.T * Ty.T

let extenv = ref Map.empty

(* for pretty printing (and type normalization) *)
let rec derefTyp = function (* ���ѿ����ȤǤ���������ؿ� (caml2html: typing_deref) *)
  | Ty.Fun(t1s, t2) -> Ty.Fun(List.map derefTyp t1s, derefTyp t2)
  | Ty.Tuple(ts) -> Ty.Tuple(List.map derefTyp ts)
  | Ty.Array(t) -> Ty.Array(derefTyp t)
  | Ty.Var({ contents = None } as r) ->
      printf "uninstantiated type variable detected; assuming int@.";
      r := Some(Ty.Int);
      Ty.Int
  | Ty.Var({ contents = Some(t) } as r) ->
      let t' = derefTyp t in
      r := Some(t');
      t'
  | t -> t
let rec derefIdTyp (x, t) = (x, derefTyp t)
let rec derefTerm = function
  | Not(e) -> Not(derefTerm e)
  | Neg(e) -> Neg(derefTerm e)
  | Add(e1, e2) -> Add(derefTerm e1, derefTerm e2)
  | Sub(e1, e2) -> Sub(derefTerm e1, derefTerm e2)
  | Eq(e1, e2) -> Eq(derefTerm e1, derefTerm e2)
  | LE(e1, e2) -> LE(derefTerm e1, derefTerm e2)
  | FNeg(e) -> FNeg(derefTerm e)
  | FAdd(e1, e2) -> FAdd(derefTerm e1, derefTerm e2)
  | FSub(e1, e2) -> FSub(derefTerm e1, derefTerm e2)
  | FMul(e1, e2) -> FMul(derefTerm e1, derefTerm e2)
  | FDiv(e1, e2) -> FDiv(derefTerm e1, derefTerm e2)
  | If(e1, e2, e3) -> If(derefTerm e1, derefTerm e2, derefTerm e3)
  | Let(xt, e1, e2) -> Let(derefIdTyp xt, derefTerm e1, derefTerm e2)
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
      LetRec({ name = derefIdTyp xt;
               args = List.map derefIdTyp yts;
               body = derefTerm e1 },
             derefTerm e2)
  | App(e, es) -> App(derefTerm e, List.map derefTerm es)
  | Tuple(es) -> Tuple(List.map derefTerm es)
  | LetTuple(xts, e1, e2) -> LetTuple(List.map derefIdTyp xts, derefTerm e1, derefTerm e2)
  | Array(e1, e2) -> Array(derefTerm e1, derefTerm e2)
  | Get(e1, e2) -> Get(derefTerm e1, derefTerm e2)
  | Put(e1, e2, e3) -> Put(derefTerm e1, derefTerm e2, derefTerm e3)
  | e -> e

let rec occur r1 =
  function (* occur check (caml2html: typing_occur) *)
  | Ty.Fun(t2s, t2) -> List.exists (occur r1) t2s || occur r1 t2
  | Ty.Tuple(t2s) -> List.exists (occur r1) t2s
  | Ty.Array(t2) -> occur r1 t2
  | Ty.Var({ contents = None }) -> false
  | Ty.Var({ contents = Some(t2) }) -> occur r1 t2
  | Ty.Var(r2) when r1 = r2 -> true
  | _ -> false

let rec unify t1 t2 = (* �����礦�褦�ˡ����ѿ�ؤ������򤹤� (caml2html: typing_unify) *)
  match t1, t2 with
  | Ty.Unit, Ty.Unit
  | Ty.Bool, Ty.Bool
  | Ty.Int, Ty.Int
  | Ty.Float, Ty.Float -> ()
  | Ty.Fun(t1s, t1'), Ty.Fun(t2s, t2') ->
      (try List.iter2 unify t1s t2s
       with _ -> raise (Unify(t1, t2)));
      unify t1' t2'
  | Ty.Tuple(t1s), Ty.Tuple(t2s) ->
      (try List.iter2 unify t1s t2s
       with _ -> raise (Unify(t1, t2)))
  | Ty.Array(t1), Ty.Array(t2) -> unify t1 t2
  | Ty.Var(r1), Ty.Var(r2) when r1 = r2 -> ()
  | Ty.Var({ contents = Some(t1') }), _ -> unify t1' t2
  | _, Ty.Var({ contents = Some(t2') }) -> unify t1 t2'
  | Ty.Var({ contents = None } as r1), _ -> (* ������̤����η��ѿ�ξ�� (caml2html: typing_undef) *)
      if occur r1 t2 then raise (Unify(t1, t2));
      r1 := Some(t2)
  | _, Ty.Var({ contents = None } as r2) ->
      if occur r2 t1 then raise (Unify(t1, t2));
      r2 := Some(t1)
  | _, _ -> raise (Unify(t1, t2))

let rec g env e = (* �������롼���� (caml2html: typing_g) *)
  try
    match e with
    | Unit -> Ty.Unit
    | Bool(_) -> Ty.Bool
    | Int(_) -> Ty.Int
    | Float(_) -> Ty.Float
    | Not(e) ->
        unify Ty.Bool (g env e);
        Ty.Bool
    | Neg(e) ->
        unify Ty.Int (g env e);
        Ty.Int
    | Add(e1, e2) | Sub(e1, e2) -> (* ­�����ʤȰ������ˤη����� (caml2html: typing_add) *)
        unify Ty.Int (g env e1);
        unify Ty.Int (g env e2);
        Ty.Int
    | FNeg(e) ->
        unify Ty.Float (g env e);
        Ty.Float
    | FAdd(e1, e2) | FSub(e1, e2) | FMul(e1, e2) | FDiv(e1, e2) ->
        unify Ty.Float (g env e1);
        unify Ty.Float (g env e2);
        Ty.Float
    | Eq(e1, e2) | LE(e1, e2) ->
        unify (g env e1) (g env e2);
        Ty.Bool
    | If(e1, e2, e3) ->
        unify (g env e1) Ty.Bool
        let t2 = g env e2
        let t3 = g env e3
        unify t2 t3;
        t2
    | Let((x, t), e1, e2) -> (* let�η����� (caml2html: typing_let) *)
        unify t (g env e1);
        g (Map.add x t env) e2
    | Var(x) when Map.containsKey x env -> Map.find x env (* �ѿ�η����� (caml2html: typing_var) *)
    | Var(x) when Map.containsKey x !extenv -> Map.find x !extenv
    | Var(x) -> (* �����ѿ�η����� (caml2html: typing_extvar) *)
        eprintf "free variable %s assumed as external@." x;
        let t = Ty.gentyp () in
        extenv := Map.add x t !extenv;
        t
    | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let rec�η����� (caml2html: typing_letrec) *)
        let env = Map.add x t env in
        unify t (Ty.Fun(List.map snd yts, g (Map.addList yts env) e1));
        g env e2
    | App(e, es) -> (* �ؿ�Ŭ�Ѥη����� (caml2html: typing_app) *)
        let t = Ty.gentyp () in
        unify (g env e) (Ty.Fun(List.map (g env) es, t));
        t
    | Tuple(es) -> Ty.Tuple(List.map (g env) es)
    | LetTuple(xts, e1, e2) ->
        unify (Ty.Tuple(List.map snd xts)) (g env e1);
        g (Map.addList xts env) e2
    | Array(e1, e2) -> (* must be a primitive for "polymorphic" typing *)
        unify (g env e1) Ty.Int;
        Ty.Array(g env e2)
    | Get(e1, e2) ->
        let t = Ty.gentyp () in
        unify (Ty.Array(t)) (g env e1);
        unify Ty.Int (g env e2);
        t
    | Put(e1, e2, e3) ->
        let t = g env e3 in
        unify (Ty.Array(t)) (g env e1);
        unify Ty.Int (g env e2);
        Ty.Unit
  with Unify(t1, t2) ->
        printfn "%A" env
        printfn "%A-%A" t1 t2
        raise (Error(derefTerm e, derefTyp t1, derefTyp t2))

let f e =
  extenv := Map.empty;
(*
  (match deref_typ (g M.empty e) with
  | Type.Unit -> ()
  | _ -> Format.eprintf "warning: final result does not have type unit@.");
*)
  (try unify Ty.Unit (g Map.empty e)
   with Unify _ ->
    failwith "top level does not have type unit");
  extenv := Map.map (fun k v -> derefTyp v) !extenv;
  derefTerm e
