module PlcInterp

open Absyn
open Environ

let rec eval (e : expr) (env : plcVal env) : plcVal =
    match e with
    | CstI i -> IntV i
    | CstB b -> BoolV b

    | Var x  ->
      let v = lookup env x in
      match v with
      | IntV  _ -> v
      | BoolV _ -> v
      | ListV  _ -> v
      | _      -> failwith ("Value of variable _" + x + "_ is not first-order.")

    | Prim1 (op, e1) ->
      let v1 = eval e1 env in
      match (op, v1) with
      | ("-", IntV i) -> IntV (- i)
      | ("!", BoolV b) -> BoolV (not b)
      | _   -> failwith "Impossible"

    | Prim2 (op, e1, e2) ->
      let v1 = eval e1 env in
      let v2 = eval e2 env in
      match (op, v1, v2) with
      | ("=", _, _) -> BoolV (v1 = v2)
      | ("<", IntV i1, IntV i2) -> BoolV (i1 < i2)
      | ("*", IntV i1, IntV i2) -> IntV (i1 * i2)
      | ("+", IntV i1, IntV i2) -> IntV (i1 + i2)
      | ("-", IntV i1, IntV i2) -> IntV (i1 - i2)
      | _   -> failwith "Impossible"

    | Let (x, e1, e2) ->
      let v = eval e1 env in
      let env2 = (x, v) :: env in
      eval e2 env2

    | If (e1, e2, e3) ->
      let v1 = eval e1 env in
      match v1 with
      | BoolV true  -> eval e2 env
      | BoolV false -> eval e3 env
      | _ -> failwith "Impossible"

    | Letfun (f, x, _, e1, _, e2) ->
      let env2 = (f, Closure(f, x, e1, env)) :: env in
      eval e2 env2

    | Call (Var f, e) ->
      let c = lookup env f in
      match c with
      | Closure (f, x, e1, fenv) ->
        let v = eval e env in
        let env1 = (x, v) :: (f, c) :: fenv in
        eval e1 env1
      | _ -> failwith "eval Call: not a function"
    | Call _ -> failwith "eval Call: not first-order function"

    | List es -> ListV (List.map (fun e -> eval e env) es)

    | Item (n, e1) ->
      match eval e1 env with
      | ListV vs -> List.item (n - 1) vs
      | _ -> failwith "Impossible"
