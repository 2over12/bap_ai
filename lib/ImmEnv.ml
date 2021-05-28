open Bap.Std


(*
Boolean variables are represented by an Envrionment s.t. bvar is true
*)
module Env = MapDomain.MakeMap(Var)(ClpDomain)

let x = 1