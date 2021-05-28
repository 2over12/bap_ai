open Bap.Std


(*
Boolean variables are represented by an Envrionment s.t. bvar is true
*)
module Env = MapDomain.MakeMap(Var)(ClpDomain)



module Immediates = ReducedProduct.MakeProduct(Env)(MapDomain.MakeMap(Var)(Env))