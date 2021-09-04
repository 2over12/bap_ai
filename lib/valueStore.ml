open Bap.Std
open Core_kernel

module MemoryRegion = struct 

  module T = struct
  type t = 
    | Heap of tid (* abstract allocation *)
    | InitReg of Var.t (* symbolic access to uninitialized variable *)
    | InitMem of Word.t (* symbolic access to unitialized memory*)
    | Global [@@deriving sexp, compare ]

  end 
  include Comparable.Make(T)
  include T
end 



module LocationDescription = struct 
  module T = struct 
    type t = {addr:int;size:int option} [@@deriving sexp, compare]
  end
  
  include Comparable.Make(T)
  include T
end


module ALoc = struct 
  
  module T = struct
      type t = 
      | Var of Var.t
      | Mem of MemoryRegion.t * LocationDescription.t [@@deriving sexp, compare]
  end 


  include Comparable.Make(T)
  include T
end


(*
Maps a MemoryRegion to possible addresses 

*)
module ValueSet = struct

  module VsetCPO = MapDomain.MakeMap(MemoryRegion)(ClpDomain)
  module VsetLattice = CompleteLattice.LatFromCPO(VsetCPO)

  include VsetLattice

 let pairwise_function_inclusive ~f:(f:ClpDomain.t -> ClpDomain.t -> ClpDomain.t) (x: t) (y:t) =
   match (x,y) with 
      | (Top,_) -> VsetLattice.Top 
      | (_,Top) -> VsetLattice.Top 
      | (Below x, Below y) -> Below (VsetCPO.pairwise_function_inclusive ~f:f x y)


 let apply_function ~f:(f: ClpDomain.t -> ClpDomain.t) = VsetLattice.fmap ~default:VsetLattice.Top ~f:(fun x -> 
  VsetLattice.Below (MemoryRegion.Map.map ~f:f x))

 let abstract_constant (w: word) = 
  (let v = CircularLinearProgression.abstract_single_value ~width:(Word.bitwidth w) (Word.to_int64 w |> Stdlib.Result.get_ok |> Z.of_int64) in
  VsetLattice.Below (MemoryRegion.Map.of_alist_exn [(MemoryRegion.Global,v)]))




end

module VariableStore = MapDomain.MakeMap(Var)(ValueSet)



module Offsets = struct 
    type t = {
      lower : Word.t;
      upper : Word.t;
    } [@@deriving compare, fields,sexp_of]
      
    type point = Word.t [@@deriving compare, sexp_of]
end

module AbstractMemory = IntervalTreeDomain.Make(Offsets)(ValueSet)


module MemoryStore  = MapDomain.MakeMap(MemoryRegion)(AbstractMemory)

module AbstractStore = ProductDomain.MakeProduct(VariableStore)(MemoryStore)


(*
module ALocMap = struct
  type t = LocationDescription.Set.t MemoryRegion.Map.t * Tid.Set.t


  let get_nearest (x: Z.t) (addrs: ClpDomain.t)= let (_,(ic,zeta)) = CircularLinearProgression.compute_gap_width_ex addrs x in CircularLinearProgression.compute_index_value addrs ic
  let get_accessed_alocs (locs: LocationDescription.Set.t) (addrs: ClpDomain.t) = 
    LocationDescription.Set.to_list locs |> List.filter_map ~f:(fun (loc: LocationDescription.t) -> 
      let near = get_nearest (Z.of_int loc.addr) addrs in
      if Z.lt near (Z.of_int loc.addr) then 
        None
    else if Z.equal near (Z.of_int loc.addr) then 
        Some (`Aligned loc)
      else if Option.is_none loc.size || Z.lt near (Z.add (Z.of_int loc.addr) (Z.of_int (Option.value_exn loc.size))) then 
        Some (`Misaligned loc)
      else
        None 
      )
    


  let location_set_to_alocs (rgn: MemoryRegion.t) (loc_set: LocationDescription.Set.t) = 
    LocationDescription.Set.fold ~init:[] ~f:(fun lst desc  -> (ALoc.Mem (rgn, desc))::lst) loc_set


  let aloc_map_to_alocs (m: LocationDescription.Set.t MemoryRegion.Map.t) = MemoryRegion.Map.fold ~f:(fun ~key:rgn ~data:loc_set total -> location_set_to_alocs rgn loc_set @ total) ~init:[] m
  
  let deref ((alocs,_): t) (maybe_vs: ValueSet.t) (sz: int) = 
    ValueSet.fmap ~default:([],aloc_map_to_alocs alocs) ~f:(fun vs ->
    MemoryRegion.Map.fold2 alocs vs ~init:([],[]) ~f:(fun ~key ~data fp -> 
      match data with
      | `Left _ -> fp
      | `Right _ -> fp
      | `Both (lset, addr) -> let (fully_accessed,partially_accesed) = fp in 
        let accessed = get_accessed_alocs lset addr in
        List.partition_map accessed ~f:(fun access -> 
          match access with 
          | `Aligned loc -> let aloc = ALoc.Mem (key,loc) in if Option.is_some loc.size && (Option.value_exn loc.size) = sz then Either.First aloc else Either.Second aloc
          | `Misaligned loc ->  let aloc = ALoc.Mem (key,loc) in Either.Second aloc
          )
      )) maybe_vs
end
*)