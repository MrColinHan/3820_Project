module Absyn

open Environ

type plcType =
    | IntT                                (*  Int                     *)
    | BoolT                               (*  Bool                    *)
    | FunT  of plcType * plcType          (*  type -> type            *)
    | ListT of plcType list               (*  Nil
                                             (type, ..., type)        *)
    | SeqT  of plcType                    (* [type]                   *)

type expr =
    | ConI   of int
    | ConB   of bool
    | ESeq   of plcType
    | Var    of string
    | Let    of string * expr * expr
    | Letrec of string * plcType * string * plcType * expr * expr
    | Prim1  of string * expr
    | Prim2  of string * expr * expr
    | If     of expr * expr * expr
    | Match  of expr * (expr option * expr) list
    | Call   of expr * expr
    | List   of expr list
    | Item   of int * expr
    | Anon   of plcType * string * expr

type plcVal =
    | BoolV of bool
    | IntV  of int
    | ListV of plcVal list
    | SeqV  of plcVal list
    | Clos  of string * string * expr * plcVal env   (* (f, x, fBody, fDeclEnv) *)

let list2string conv sep l =
    let conc s t = s + sep + conv t
    match l with
    | []      -> ""
    | v :: vs -> List.fold conc (conv v) vs

let rec type2string t =
    match t with
    | BoolT         -> "Bool"
    | IntT          -> "Int"
    | ListT []      -> "Nil"
    | ListT ts      -> "(" + list2string type2string ", " ts + ")"
    | SeqT t1       -> "[" + type2string t1 + "]"
    | FunT (t1, t2) ->
        match t1 with
        | FunT _ -> "(" + type2string t1 + ") -> " + type2string t2
        | _      ->       type2string t1 +  " -> " + type2string t2

let rec val2string v =
    match v with
    | BoolV true  -> "true"
    | BoolV false -> "false"
    | IntV n      -> string n
    | ListV vs    -> "(" + list2string val2string ", " vs + ")"
    | SeqV vs     -> "[" + list2string val2string "; " vs + "]"
    | Clos _      -> "<fun>"
