module Closure
type Closure
    = { entry       : Id.L
        actual_fv   : Id.T list }

type T = (* ���������Ѵ���μ� (caml2html: closure_t) *)
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
  | IfEq of Id.T * Id.T * T * T
  | IfLE of Id.T * Id.T * T * T
  | Let of (Id.T * Ty.T) * T * T
  | Var of Id.T
  | MakeCls of (Id.T * Ty.T) * Closure * T
  | AppCls of Id.T * Id.T list
  | AppDir of Id.L * Id.T list
  | Tuple of Id.T list
  | LetTuple of (Id.T * Ty.T) list * Id.T * T
  | Get of Id.T * Id.T
  | Put of Id.T * Id.T * Id.T
  | ExtArray of Id.L
type FunDef = { name : Id.L * Ty.T;
                args : (Id.T * Ty.T) list;
                formal_fv : (Id.T * Ty.T) list;
                body : T }
type Prog = Prog of FunDef list * T

let rec fv = function
  | Unit | Int(_) | Float(_) | ExtArray(_) -> Set.empty
  | Neg(x) | FNeg(x) -> Set.singleton x
  | Add(x, y) | Sub(x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> Set.ofList [x; y]
  | IfEq(x, y, e1, e2)| IfLE(x, y, e1, e2) -> Set.add x (Set.add y (Set.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> Set.union (fv e1) (Set.remove x (fv e2))
  | Var(x) -> Set.singleton x
  | MakeCls((x, t), { entry = l; actual_fv = ys }, e) -> Set.remove x (Set.union (Set.ofList ys) (fv e))
  | AppCls(x, ys) -> Set.ofList (x :: ys)
  | AppDir(_, xs) | Tuple(xs) -> Set.ofList xs
  | LetTuple(xts, y, e) -> Set.add y (Set.difference (fv e) (Set.ofList (List.map fst xts)))
  | Put(x, y, z) -> Set.ofList [x; y; z]

let toplevel : FunDef list ref = ref []

let rec g env known = function (* ���������Ѵ��롼�������� (caml2html: closure_g) *)
  | KNormal.Unit -> Unit
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Neg(x) -> Neg(x)
  | KNormal.Add(x, y) -> Add(x, y)
  | KNormal.Sub(x, y) -> Sub(x, y)
  | KNormal.FNeg(x) -> FNeg(x)
  | KNormal.FAdd(x, y) -> FAdd(x, y)
  | KNormal.FSub(x, y) -> FSub(x, y)
  | KNormal.FMul(x, y) -> FMul(x, y)
  | KNormal.FDiv(x, y) -> FDiv(x, y)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g env known e1, g env known e2)
  | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g env known e1, g env known e2)
  | KNormal.Let((x, t), e1, e2) -> Let((x, t), g env known e1, g (Map.add x t env) known e2)
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) -> (* �ؿ�����ξ�� (caml2html: closure_letrec) *)
      (* �ؿ����let rec x y1 ... yn = e1 in e2�ξ��ϡ�
         x�˼�ͳ�ѿ�ʤ�(closure��𤵤�direct�˸ƤӽФ���)
         �Ȳ��ꤷ��known���ɲä���e1�򥯥������Ѵ����Ƥߤ� *)
      let toplevel_backup = !toplevel in
      let env' = Map.add x t env in
      let known' = Set.add x known in
      let e1' = g (Typing.Map.addList yts env') known' e1 in
      (* �����˼�ͳ�ѿ�ʤ��ä������Ѵ����e1'���ǧ���� *)
      (* ���: e1'��x���Ȥ��ѿ�Ȥ��ƽи��������closure��ɬ��!
         (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml����) *)
      let zs = Set.difference (fv e1') (Set.ofList (List.map fst yts)) in
      let known', e1' =
        if Set.isEmpty zs then known', e1' else
        (* ���ܤ��ä������(toplevel����)���ᤷ�ơ����������Ѵ�����ľ�� *)
        (printf "free variable(s) %s found in function %s@." (Id.ppList (Set.toList zs)) x;
         printf "function %s cannot be directly applied in fact@." x;
         toplevel := toplevel_backup;
         let e1' = g (Typing.Map.addList yts env') known e1 in
         known, e1') in
      let zs = Set.toList (Set.difference (fv e1') (Set.add x (Set.ofList (List.map fst yts)))) in (* ��ͳ�ѿ�Υꥹ�� *)
      let zts = List.map (fun z -> (z, Map.find z env')) zs in (* �����Ǽ�ͳ�ѿ�z�η����������˰���env��ɬ�� *)
      toplevel := { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e1' } :: !toplevel; (* �ȥåץ�٥�ؿ���ɲ� *)
      let e2' = g env' known' e2 in
      if Set.contains x (fv e2') then (* x���ѿ�Ȥ���e2'�˽и����뤫 *)
        MakeCls((x, t), { entry = Id.L(x); actual_fv = zs }, e2') (* �и����Ƥ����������ʤ� *)
      else
        (printf "eliminating closure(s) %s@." x;
         e2') (* �и����ʤ����MakeCls���� *)
  | KNormal.App(x, ys) when Set.contains x known -> (* �ؿ�Ŭ�Ѥξ�� (caml2html: closure_app) *)
      printf "directly applying %s@." x;
      AppDir(Id.L(x), ys)
  | KNormal.App(f, xs) -> AppCls(f, xs)
  | KNormal.Tuple(xs) -> Tuple(xs)
  | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (Typing.Map.addList xts env) known e)
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.ExtArray(x) -> ExtArray(Id.L(x))
  | KNormal.ExtFunApp(x, ys) -> AppDir(Id.L("min_caml_" + x), ys)

let f e =
  toplevel := [];
  let e' = g Map.empty Set.empty e in
  Prog(List.rev !toplevel, e')
