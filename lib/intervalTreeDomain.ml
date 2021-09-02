(*
Disjunction domain of array accesses where array is of inifinite size


Sources for array abstractionsz

https://www.microsoft.com/en-us/research/wp-content/uploads/2011/01/POPL090-Cousot-Cousot-Logozzo.pdf

So there are two ways to do this... either we have some quick array domain and just do that and then ASI afterwards to recover variable like alocs

or we do it here. I think the easiest way is to try to use traditional array modeling techniques to help propogate 
points to relations then generate DAC constraints
*)

open Bap.Std
open Core_kernel
open Regular.Std


module type CPO = sig 
  include AbstractDomain.CPO
end



module Make(IK: Interval_tree.Interval)(X: CPO) = struct
  module Tree = Interval_tree.Make(IK)  


  module T = struct 
    type cell = {elem: X.t; size: int } [@@deriving sexp_of]

    type t = cell Tree.t [@@deriving sexp_of]


    (* lets first ask the question of if we can handle a single tree
      so if every every interval in t1 is equal to an interval in t2 and the value is le 
        then it is le    
    
    hmm this doesnt handle the width of each cell

    fortunately le is the only operation that matters here infact it should be the only thing we implement 
interfaces need to change
      *)
    let le (t1:t) (t2: t) =  
      let ts_seq = Tree.to_sequence t1 in 
      let t2_has_equal_key t1_key value = Seq.exists (Tree.intersections t2 t1_key) ~f:(fun (k2, v2) -> (Int.equal
       (IK.compare t1_key k2) 0) && Int.equal value.size v2.size && X.le value.elem v2.elem)  in
      Seq.for_all ts_seq ~f:(fun (k,v)  -> t2_has_equal_key k v)
      

    let eq (t1: t) (t2: t) =       
      le t1 t2


      (* not there is potential to be incomparable and thes will get classified as GT*)
    let compare (t1: t) (t2: t) = 
      if eq t1 t2 then 
        0
      else if le t1 t2 then 
        -1
      else 
        1  
    (*
    let compare (t1: X.t Tree.t) (t2: X.t Tree.t) = 
      
      let exact_binding_k k = t2 in 
      Seq.all exact_binding_k (Tree.to_sequence t1)*)

    let t_of_sexp = raise (Failure "parsing not implemented")
  end

  include Comparable.Make(T)
  include T

  (*
  plan ok split into sets where have all keys that overlap in anyways in a tree 
  *)
  let join  (t1: t) (t2: t) = 
    if le t1 t2 then 
      t2 else if le t2 t1 then t1
      else  

end