module Plc

open Absyn
open PlcInterp
open PlcChecker

let run (e: expr) =
    let t = teval e []
    let v = eval e []
    (val2string v) + " : " + (type2string t)
