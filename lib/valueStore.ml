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

module ValueSet = MapDomain.MakeMap(MemoryRegion)(ClpDomain) 


module AbstractStore = MapDomain.MakeMap(ALoc)(ValueSet)