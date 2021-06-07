open Core_kernel





module LatFromCPO(X: AbstractDomain.CPO) = struct 



  module T = struct 
  type t =  | Top 
            | Below of X.t [@@deriving sexp, compare]
  end

  include Comparable.Make(T)
  include T

  let fmap (elem:t) ~f:(f: X.t -> 'a) ~default:(default:'a) = match elem with 
    | Top -> default
    | Below x -> f x

  let top = Top  
  let widen a1 a2 = match (a1,a2) with 
    | (Top,_) -> Top
    | (_,Top) -> Top
    | (Below x, Below y) -> Below (X.widen x y ) 

  let narrow a b = match (a,b) with
    | (Top, a2) -> a2
    | (a1,Top) -> a1
    | (Below x, Below y) -> Below (X.narrow x y) 


  let meet x y = match (x,y) with 
    | (Top,sm) -> sm
    | (sm, Top) -> sm
    | (Below a1, Below a2) -> Below (X.meet a1 a2)
 

  let join x y = match (x,y) with 
    | (Top,_) -> Top
    | (_, Top) -> Top
    | (Below a1, Below a2) -> Below (X.join a1 a2)

  let bot = Below X.bot

  let le x y = match (x,y) with
    | (Top, Below _) -> false
    | (Below _, Top) -> true
    | (Top, Top) -> true
    | (Below a1, Below a2) -> X.le a1 a2


  let eq x y = match (x,y) with
  | (Top, Below _) -> false
  | (Below _, Top) -> false
  | (Top, Top) -> true
  | (Below a1, Below a2) -> X.eq a1 a2
 
end