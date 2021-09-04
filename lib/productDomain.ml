open Core_kernel

module type CPO = sig 
  include AbstractDomain.CPO
end



module MakeProductWithReduction(X: AbstractDomain.CPO)(Y: AbstractDomain.CPO)(R: sig 
  val reduce:  X.t * Y.t -> X.t * Y.t
  end) = struct 

    include Tuple.Make(X)(Y)
    include Tuple.Sexpable(X)(Y)
  
  
    let bi_apply (f1, f2) (arg1,arg2) = (f1 arg1, f2 arg2)
  
      
  
    let apply ~fx ~fy f s = (Tuple.T2.map_fst f ~f:fx |> Tuple.T2.map_snd ~f:fy |> bi_apply) s
  
  
    let apply_and_reduce ~fx ~fy f  s = apply ~fx:fx ~fy:fy f s |> R.reduce
  
    let narrow = apply_and_reduce ~fx:X.narrow ~fy:Y.narrow
  
    let widen = apply_and_reduce ~fx:X.widen ~fy:Y.widen
  
    let join = apply_and_reduce ~fx:X.join ~fy:Y.join
  
    let bot = (X.bot,Y.bot)
  
    let meet = apply_and_reduce ~fx:X.meet ~fy:Y.meet
  
    let le f s = let (le1, le2) = apply ~fx:X.le ~fy:Y.le f s in le1 && le2
  
    let eq f s = let (le1, le2) = apply ~fx:X.eq ~fy:Y.eq f s in le1 && le2
  end
  
  


module MakeProduct(X:  AbstractDomain.CPO)(Y: AbstractDomain.CPO) = struct 

include MakeProductWithReduction(X)(Y)(struct 
  let reduce a = a
end)

end


module BottomReduction (X: AbstractDomain.CPO)(Y: AbstractDomain.CPO) = struct
  include MakeProductWithReduction(X)(Y)(struct 
  let reduce (x,y) = if X.eq X.bot x || Y.eq Y.bot y then (X.bot, Y.bot) else (x,y)
end)
end