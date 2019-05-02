module ParAux

open Absyn

let l =  "$list"
let elist =  "()"

let rec makeFunAux (n: int) (xs: (plcType * string) list) (e: expr) : expr =
    // TODO
    match xs with 
    | []          -> e
    | (t, x) :: r -> Let (x, Item (n, Var l), makeFunAux (n + 1) r e)

let makeType (args: (plcType * string) list): plcType =
    // TODO
    ListT (List.map (fun (x,y) -> x) args)

let makeFun (f: string) (xs: (plcType * string) list) (rt: plcType) (e1: expr) (e2: expr) : expr =
    match xs with
    | []           -> Letrec (f, ListT [], elist, rt, e1, e2)
    | (t, x) :: [] -> Letrec (f, t, x, rt, e1, e2)
    | _            ->
        let t = makeType xs in
        let e1' = makeFunAux 1 xs e1 in
        Letrec(f, t, l, rt, e1', e2)

let makeAnon (xs: (plcType * string) list) (e: expr) : expr =
    match xs with
    | []           -> Anon (ListT [], elist, e)
    | (t, x) :: [] -> Anon (t, x, e)
    | _            ->
        let t = makeType xs in
        let e' = makeFunAux 1 xs e in
        Anon (t, l, e')
