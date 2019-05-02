
module PlcChecker

open Absyn
open Environ

(* Type checker for the first-order version of Micro-ML *)

// The type checker can be seen as an interpreter that computes
// the type of an expression instead of its value.

let rec teval (e : expr) (env : plcType env) : plcType =
    match e with
    | CstI i -> IntT

    | CstB b -> BoolT

    | Var x  -> lookup env x

    | Prim1 (op, e1) ->
      let t1 = teval e1 env in
      match (op, t1) with
      | ("-", IntT) -> IntT
      | ("!", BoolT) -> BoolT
      | _   -> failwith "Checker: unknown op, or type error"

    | Prim2 (op, e1, e2) ->
      let t1 = teval e1 env in
      let t2 = teval e2 env in
      match (op, t1, t2) with
      | ("*", IntT, IntT) -> IntT
      | ("+", IntT, IntT) -> IntT
      | ("-", IntT, IntT) -> IntT
      | ("<", IntT, IntT) -> BoolT
      | ("=", t1, t2) when t1 = t2 -> BoolT

      | _   -> failwith "Checker: unknown op, or type error"

    | Let (x, e1, e2) ->
      let t = teval e1 env in
      let env' = (x, t) :: env in
      teval e2 env'

    | If (e1, e2, e3) ->
      match teval e1 env with
      | BoolT -> let t2 = teval e2 env in
                 let t3 = teval e3 env in
                 if t2 = t3 then
                   t2
                 else
                   failwith "Checker: 'if' branch types differ"

      | _    -> failwith "Checker: 'if':' condition not Boolean"

    | Letfun (f, x, xt, e1, rt, e2) ->
      let ft = FunT (xt, rt) in
      let fenv = (x, xt) :: (f, ft) :: env in
      let lenv = (f, ft) :: env in
      if teval e1 fenv = rt then
        teval e2 lenv
      else
        failwith ("Checker: wrong return type in function " + f)

    | Call (Var f, e) ->
      match lookup env f with
      | FunT (xt, rt) ->
        if teval e env = xt then
          rt
        else
          failwith "Checker: type mismatch in function call"
      | _ -> failwith ("Checker: function " + f + "is undefined")

    | Call _ -> failwith "Call: illegal function in call"

    | List es -> ListT (List.map (fun e -> teval e env) es)

    | Item (i, e1) ->
      match teval e1 env with
      | ListT ts ->
        if 0 < i && i <= List.length ts then
          List.item (i - 1) ts
        else
          failwith "Checker: List index out of range"
      | _ -> failwith ("Checker: access operator [" + string i + "] applied to non-list")


