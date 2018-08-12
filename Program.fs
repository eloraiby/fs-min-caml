// Learn more about F# at http://fsharp.org

open System
open System.IO
open Microsoft.FSharp.Text.Lexing
let limit = ref 1000

let rec iter n e = (* ��Ŭ�������򤯤꤫���� (caml2html: main_iter) *)
  eprintf "iteration %d@." n;
  if n = 0 then e else
  let e' = Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e)))) in
  if e = e' then e else
  iter (n - 1) e'

let lexbuf l = (* �Хåե��򥳥�ѥ��뤷�ƥ����ͥ�ؽ��Ϥ��� (caml2html: main_lexbuf) *)
    Id.counter := 0;
    Typing.extenv := Map.empty;

    (Closure.f
        (iter !limit
           (Alpha.f
              (KNormal.f
                 (Typing.f
                    (Parser.exp Lexer.token l))))))

let test = """
let rec fib n =
  if n <= 1 then n else
  fib (n - 1) + fib (n - 2) in
print_int (fib 10)
"""
[<EntryPoint>]
let main argv =
    let lb = LexBuffer<char>.FromString test
    printfn "%A" (lexbuf lb)
    0 // return an integer exit code
