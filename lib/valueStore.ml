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

module ValueSet = struct
 include MapDomain.MakeMap(MemoryRegion)(ClpDomain) 

 let abstract_constant (w: word) = 
  (let v = CircularLinearProgression.abstract_single_value ~width:(Word.bitwidth w) (Word.to_int64 w |> Stdlib.Result.get_ok |> Z.of_int64) in
  MemoryRegion.Map.of_alist_exn [(MemoryRegion.Global,v)])



end

module AbstractStore = MapDomain.MakeMap(ALoc)(ValueSet)



module AlocMap = struct
  type t = LocationDescription.Set.t MemoryRegion.Map.t


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
    
  
  let deref (alocs: t) (vs: ValueSet.t) (sz: int) = 
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
      )
end