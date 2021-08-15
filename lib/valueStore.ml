open Bap.Std
open Core_kernel



(*
@inproceedings{10.1145/3015135.3015137,
author = {Feist, Josselin and Mounier, Laurent and Bardin, S\'{e}bastien and David, Robin and Potet, Marie-Laure},
title = {Finding the Needle in the Heap: Combining Static Analysis and Dynamic Symbolic Execution to Trigger Use-after-Free},
year = {2016},
isbn = {9781450348416},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
url = {https://doi.org/10.1145/3015135.3015137},
doi = {10.1145/3015135.3015137},
abstract = {This paper presents a fully automated technique to find and trigger Use-After-Free
vulnerabilities (UAF) on binary code. The approach combines a static analyzer and
a dynamic symbolic execution engine. We also introduce several original heuristics
for the dynamic symbolic execution part, speeding up the exploration and making this
combination effective in practice. The tool we developed is open-source, and it has
successfully been applied on real world vulnerabilities. As an example, we detail
a proof-of-concept exploit triggering a previously unknown vulnerability on JasPer
leading to the CVE-2015-5221.},
booktitle = {Proceedings of the 6th Workshop on Software Security, Protection, and Reverse Engineering},
articleno = {2},
numpages = {12},
keywords = {dynamic symbolic execution, binary code analysis, vulnerability detection, use-after-free, automated exploit generation},
location = {Los Angeles, California, USA},
series = {SSPREW '16}
}


We take an approach similar to this paper where we have a a-locs for unitialized registers
wherein <init_reg, offset>


K. Anand, K. Elwazeer, A. Kotha, M. Smithson, R. Barua and A. Keromytis, "An Accurate Stack Memory Abstraction and Symbolic Analysis Framework for Executables," 2013 IEEE International Conference on Software Maintenance, 2013, pp. 90-99, doi: 10.1109/ICSM.2013.20.

This paper proposes a stack model.

*)
  

module MemoryRegion = struct 

  module T = struct
  type t = 
    | Heap of tid (* abstract allocation *)
    | Init of Var.t (* stack of a procedure *)
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
  module VsetCPO = MapDomain.MakeMap(MemoryRegion)(ClpDomain)
  include CompleteLattice.LatFromCPO(VsetCPO)
  
 let pairwise_function_inclusive ~f:(f:ClpDomain.t -> ClpDomain.t -> ClpDomain.t) (x: t) (y:t) =
    match (x,y) with 
      | (Top,_) -> Top 
      | (_,Top) -> Top 
      | (Below x, Below y) -> Below (VsetCPO.pairwise_function_inclusive ~f:f x y)


 let apply_function ~f:(f: ClpDomain.t -> ClpDomain.t) = fmap ~default:Top ~f:(fun x -> 
  Below (MemoryRegion.Map.map ~f:f x))

 let abstract_constant (w: word) = 
  (let v = CircularLinearProgression.abstract_single_value ~width:(Word.bitwidth w) (Word.to_int64 w |> Stdlib.Result.get_ok |> Z.of_int64) in
  Below (MemoryRegion.Map.of_alist_exn [(MemoryRegion.Global,v)]))

end

module AbstractStore = MapDomain.MakeMap(ALoc)(ValueSet)


(*stores results of preanalysis*)
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