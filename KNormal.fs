module KNormal

(* give names to intermediate values (K-normalization) *)

type T = (* K��������μ� (caml2html: knormal_t) *)
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.T
  | Add of Id.T * Id.T
  | Sub of Id.T * Id.T
  | FNeg of Id.T
  | FAdd of Id.T * Id.T
  | FSub of Id.T * Id.T
  | FMul of Id.T * Id.T
  | FDiv of Id.T * Id.T
  | IfEq of Id.T * Id.T * T * T (* ��� + ʬ�� (caml2html: knormal_branch) *)
  | IfLE of Id.T * Id.T * T * T (* ��� + ʬ�� *)
  | Let of (Id.T * Ty.T) * T * T
  | Var of Id.T
  | LetRec of FunDef * T
  | App of Id.T * Id.T list
  | Tuple of Id.T list
  | LetTuple of (Id.T * Ty.T) list * Id.T * T
  | Get of Id.T * Id.T
  | Put of Id.T * Id.T * Id.T
  | ExtArray of Id.T
  | ExtFunApp of Id.T * Id.T list
and FunDef = { name : Id.T * Ty.T; args : (Id.T * Ty.T) list; body : T }

let rec fv = function (* ���˽и�����ʼ�ͳ�ʡ��ѿ� (caml2html: knormal_fv) *)
  | Unit | Int(_) | Float(_) | ExtArray(_) -> Set.empty
  | Neg(x) | FNeg(x) -> Set.singleton x
  | Add(x, y) | Sub(x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> Set.ofList [x; y]
  | IfEq(x, y, e1, e2) | IfLE(x, y, e1, e2) -> Set.add x (Set.add y (Set.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> Set.union (fv e1) (Set.remove x (fv e2))
  | Var(x) -> Set.singleton x
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
      let zs = Set.difference (fv e1) (Set.ofList (List.map fst yts)) in
      Set.difference (Set.union zs (fv e2)) (Set.singleton x)
  | App(x, ys) -> Set.ofList (x :: ys)
  | Tuple(xs) | ExtFunApp(_, xs) -> Set.ofList xs
  | Put(x, y, z) -> Set.ofList [x; y; z]
  | LetTuple(xs, y, e) -> Set.add y (Set.difference (fv e) (Set.ofList (List.map fst xs)))

let insertLet (e, t) k = (* let��������������ؿ� (caml2html: knormal_insert) *)
  match e with
  | Var(x) -> k x
  | _ ->
      let x = Id.gentmp t in
      let e', t' = k x in
      Let((x, t), e, e'), t'

let rec g env = function (* K�������롼�������� (caml2html: knormal_g) *)
  | Syntax.Unit -> Unit, Ty.Unit
  | Syntax.Bool(b) -> Int(if b then 1 else 0), Ty.Int (* ������true, false������1, 0���Ѵ� (caml2html: knormal_bool) *)
  | Syntax.Int(i) -> Int(i), Ty.Int
  | Syntax.Float(d) -> Float(d), Ty.Float
  | Syntax.Not(e) -> g env (Syntax.If(e, Syntax.Bool(false), Syntax.Bool(true)))
  | Syntax.Neg(e) ->
      insertLet (g env e)
        (fun x -> Neg(x), Ty.Int)
  | Syntax.Add(e1, e2) -> (* ­������K������ (caml2html: knormal_add) *)
      insertLet (g env e1)
        (fun x -> insertLet (g env e2)
                    (fun y -> Add(x, y), Ty.Int))
  | Syntax.Sub(e1, e2) ->
      insertLet (g env e1)
        (fun x -> insertLet (g env e2)
                    (fun y -> Sub(x, y), Ty.Int))
  | Syntax.FNeg(e) ->
      insertLet (g env e)
        (fun x -> FNeg(x), Ty.Float)
  | Syntax.FAdd(e1, e2) ->
      insertLet (g env e1)
        (fun x -> insertLet (g env e2)
                    (fun y -> FAdd(x, y), Ty.Float))
  | Syntax.FSub(e1, e2) ->
      insertLet (g env e1)
        (fun x -> insertLet (g env e2)
                    (fun y -> FSub(x, y), Ty.Float))
  | Syntax.FMul(e1, e2) ->
      insertLet (g env e1)
        (fun x -> insertLet (g env e2)
                    (fun y -> FMul(x, y), Ty.Float))
  | Syntax.FDiv(e1, e2) ->
      insertLet (g env e1)
        (fun x -> insertLet (g env e2)
                    (fun y -> FDiv(x, y), Ty.Float))
  | Syntax.Eq _ | Syntax.LE _ as cmp ->
      g env (Syntax.If(cmp, Syntax.Bool(true), Syntax.Bool(false)))
  | Syntax.If(Syntax.Not(e1), e2, e3) -> g env (Syntax.If(e1, e3, e2)) (* not�ˤ��ʬ����Ѵ� (caml2html: knormal_not) *)
  | Syntax.If(Syntax.Eq(e1, e2), e3, e4) ->
      insertLet (g env e1)
        (fun x -> insertLet (g env e2)
                     (fun y ->
                          let e3', t3 = g env e3 in
                          let e4', t4 = g env e4 in
                          IfEq(x, y, e3', e4'), t3))
  | Syntax.If(Syntax.LE(e1, e2), e3, e4) ->
      insertLet (g env e1)
        (fun x -> insertLet (g env e2)
                     (fun y ->
                          let e3', t3 = g env e3 in
                          let e4', t4 = g env e4 in
                          IfLE(x, y, e3', e4'), t3))
  | Syntax.If(e1, e2, e3) -> g env (Syntax.If(Syntax.Eq(e1, Syntax.Bool(false)), e3, e2)) (* ��ӤΤʤ�ʬ����Ѵ� (caml2html: knormal_if) *)
  | Syntax.Let((x, t), e1, e2) ->
      let e1', t1 = g env e1 in
      let e2', t2 = g (Map.add x t env) e2 in
      Let((x, t), e1', e2'), t2
  | Syntax.Var(x) when Map.containsKey x env -> Var(x), Map.find x env
  | Syntax.Var(x) -> (* ��������λ��� (caml2html: knormal_extarray) *)
      (match Map.find x !Typing.extenv with
      | Ty.Array(_) as t -> ExtArray x, t
      | _ -> failwith (Printf.sprintf "external variable %s does not have an array type" x))
  | Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2) ->
      let env' = Map.add x t env in
      let e2', t2 = g env' e2 in
      let e1', t1 = g (Typing.Map.addList yts env') e1 in
      LetRec({ name = (x, t); args = yts; body = e1' }, e2'), t2
  | Syntax.App(Syntax.Var(f), e2s) when not (Map.containsKey f env) -> (* ����ؿ�θƤӽФ� (caml2html: knormal_extfunapp) *)
      (match Map.find f !Typing.extenv with
      | Ty.Fun(_, t) ->
          let rec bind xs = function (* "xs" are identifiers for the arguments *)
            | [] -> ExtFunApp(f, xs), t
            | e2 :: e2s ->
                insertLet (g env e2)
                  (fun x -> bind (xs @ [x]) e2s) in
          bind [] e2s (* left-to-right evaluation *)
      | _ -> failwith "unable to normalize application")
  | Syntax.App(e1, e2s) ->
      (match g env e1 with
      | _, Ty.Fun(_, t) as g_e1 ->
          insertLet g_e1
            (fun f ->
              let rec bind xs = function (* "xs" are identifiers for the arguments *)
                | [] -> App(f, xs), t
                | e2 :: e2s ->
                    insertLet (g env e2)
                      (fun x -> bind (xs @ [x]) e2s) in
              bind [] e2s) (* left-to-right evaluation *)
      | _ -> failwith "unable to normalize application")
  | Syntax.Tuple(es) ->
      let rec bind xs ts = function (* "xs" and "ts" are identifiers and types for the elements *)
        | [] -> Tuple(xs), Ty.Tuple(ts)
        | e :: es ->
            let _, t as g_e = g env e in
            insertLet g_e
              (fun x -> bind (xs @ [x]) (ts @ [t]) es) in
      bind [] [] es
  | Syntax.LetTuple(xts, e1, e2) ->
      insertLet (g env e1)
        (fun y ->
          let e2', t2 = g (Typing.Map.addList xts env) e2 in
          LetTuple(xts, y, e2'), t2)
  | Syntax.Array(e1, e2) ->
      insertLet (g env e1)
        (fun x ->
          let _, t2 as g_e2 = g env e2 in
          insertLet g_e2
            (fun y ->
              let l =
                match t2 with
                | Ty.Float -> "create_float_array"
                | _ -> "create_array" in
              ExtFunApp(l, [x; y]), Ty.Array(t2)))
  | Syntax.Get(e1, e2) ->
      (match g env e1 with
      |        _, Ty.Array(t) as ge1 ->
          insertLet ge1
            (fun x -> insertLet (g env e2)
                        (fun y -> Get(x, y), t))
      | _ -> failwith "invalid get")
  | Syntax.Put(e1, e2, e3) ->
      insertLet (g env e1)
        (fun x -> insertLet (g env e2)
                    (fun y -> insertLet (g env e3)
                                (fun z -> Put(x, y, z), Ty.Unit)))

let f e = fst (g Map.empty e)
