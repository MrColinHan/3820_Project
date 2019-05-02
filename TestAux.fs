module TestAux

open Microsoft.FSharp.Text
open Absyn
open PlcParser

let insCaret (s: string) r c =
  let mutable s' = "" in
  let mutable r' = 1 in
  let mutable l = [] in
  let ins r1 r2 = 
    if r1 = r2 
      then String.replicate c " " + "^" :: s' :: l 
      else s' :: l
  in
    for ch in s do
      if ch = '\n' then
        l <- ins r r'
        s' <- ""
        r' <- r' + 1
      else   
        s' <- s' + string ch
    ;
    List.fold (fun x y -> y + "\n" + x) "" (ins r r')

let test (s:string, e:expr) = 
  let lexbuf = Lexing.LexBuffer<char>.FromString(s) in
  try 
    let e1 = PlcParser.Main PlcLexer.Token lexbuf in
    if e = e1 then 0
    else
      printfn "\nAbstract syntax mismatch for program:\n\n\"%s\"" s; 
      printfn "\nExpected:\n%A" e; 
      printfn "\nGenerated:\n%A" e1;       
      1
  with 
  | exn -> let pos = lexbuf.EndPos in
           let r = pos.Line + 1 in
           let c = if pos.Column > 1 then pos.Column - 2 else pos.Column in
           let s' = insCaret s r c in
           printfn "\n%s near line %d, column %d of program:\n\n\"%s\"" 
                     (exn.Message) r c s';
           1

let testAll tm = 
  printfn "---------------------------------------------------------------------------";
  let len = List.length tm in
  let n = List.fold (fun x y -> x + test y) 0 tm in
  printfn "\n---------------------------------------------------------------------------";
  printfn "  Total number of failed tests: %d/%d" n len;
  printfn "---------------------------------------------------------------------------";
  n
