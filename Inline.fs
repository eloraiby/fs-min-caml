module Inline

open KNormal

(* ����饤��Ÿ������ؿ�κ��祵���� (caml2html: inline_threshold) *)
let threshold = ref 0 (* Main��-inline���ץ����ˤ�ꥻ�åȤ���� *)

let rec size = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2)
  | Let(_, e1, e2) | LetRec({ body = e1 }, e2) -> 1 + size e1 + size e2
  | LetTuple(_, _, e) -> 1 + size e
  | _ -> 1

let rec g env = function (* ����饤��Ÿ���롼�������� (caml2html: inline_g) *)
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env e1, g env e2)
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env e1, g env e2)
  | Let(xt, e1, e2) -> Let(xt, g env e1, g env e2)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* �ؿ�����ξ�� (caml2html: inline_letrec) *)
      let env = if size e1 > !threshold then env else Map.add x (yts, e1) env in
      LetRec({ name = (x, t); args = yts; body = g env e1}, g env e2)
  | App(x, ys) when Map.containsKey x env -> (* �ؿ�Ŭ�Ѥξ�� (caml2html: inline_app) *)
      let (zs, e) = Map.find x env in
      eprintf "inlining %s@." x;
      let env' =
        List.fold2//fold_left2
          (fun env' (z, t) y -> Map.add z y env')
          Map.empty
          zs
          ys in
      Alpha.g env' e
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env e)
  | e -> e

let f e = g Map.empty e
