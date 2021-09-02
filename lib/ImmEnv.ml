open Bap.Std


(*
this is kinda weird cause the only thing affected is going to be constraints on the global value of involved variables

this does avoid code reuse
*)


module BooleanImmediates = MapDomain.MakeMap(Var)(ProductDomain.MakeProduct(ValueStore.AbstractStore)(ValueStore.AbstractStore))
