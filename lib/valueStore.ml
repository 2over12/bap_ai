open Bap.Std
open Core_kernel

module MemoryRegion = struct 

  module T = struct
  type t = 
    | Heap of tid (* abstract allocation *)
    | Stack of tid (* stack of a procedure *)
    | Global [@@deriving sexp, compare ]

  end 
  include Comparable.Make(T)
  include T
end 


module ALoc = struct 
  type location_description = {addr:int;size:int option} [@@deriving sexp, compare]
  module T = struct
      type t = 
      | Var of Var.t
      | Mem of MemoryRegion.t * location_description [@@deriving sexp, compare]
  end 


  include Comparable.Make(T)
  include T
end

module ValueSet = struct
 include MapDomain.MakeMap(MemoryRegion)(ClpDomain) 

 let abstract_constant (w: word) = 
  (let v = CircularLinearProgression.abstract_single_value ~width:(Word.bitwidth w) (Word.to_int64 w |> Stdlib.Result.get_ok |> Z.of_int64) in
  MemoryRegion.Map.of_alist_exn [(MemoryRegion.Global,v)])



end

module AbstractStore = MapDomain.MakeMap(ALoc)(ValueSet)