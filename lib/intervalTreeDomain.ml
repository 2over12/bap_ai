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




module type Bitwdith_CPO = sig 
  include CPO
  
  val bitwidth: t -> int
end


(*
Summarizes non-overlapping regions by elements in X

Invariants:
- non-overlapping regions
- All IK in 
*)
module Make(IK: Interval_tree.Interval)(X: CPO) = struct
  module Tree = Interval_tree.Make(IK)  


  module T = struct 
    type cell = {width: int; elem: X.t} [@@deriving sexp_of]
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
       (IK.compare t1_key k2) 0) && Int.equal value.width v2.width && X.le value.elem v2.elem)  in
      Seq.for_all ts_seq ~f:(fun (k,v)  -> t2_has_equal_key k v)
      

    let eq (t1: t) (t2: t) =       
      le t1 t2 && le t2 t1


 
    (*
    let compare (t1: X.t Tree.t) (t2: X.t Tree.t) = 
      
      let exact_binding_k k = t2 in 
      Seq.all exact_binding_k (Tree.to_sequence t1)*)

    let t_of_sexp = raise (Failure "parsing not implemented")
  end

  include T

  (*
  plan ok split into sets where have all keys that overlap in anyways in a tree 
  *)
  let join  (t1: t) (t2: t) = 
    if le t1 t2 then 
      t2 else if le t2 t1 then t1
      else  
        raise (Failure "havent figured this out yet")


  let narrow t1 t2 = raise (Failure "unimplemented") 

  let meet t1 t2 = raise (Failure "unimplemented") 


  let widen t1 t2 = raise (Failure "unimplemented") 

  let bot = raise (Failure "unimplemented") 
end