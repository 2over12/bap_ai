
 
module MakeProduct(X: AbstractDomain.CPO)(Y: AbstractDomain.CPO): sig 
  include AbstractDomain.CPO with type t = X.t * Y.t
end


module MakeProductWithReduction(X: AbstractDomain.CPO)(Y: AbstractDomain.CPO)(R: sig 
val reduce:  X.t * Y.t -> X.t * Y.t
end): sig 
  include AbstractDomain.CPO with type t = X.t * Y.t
end


module BottomReduction (X: AbstractDomain.CPO)(Y: AbstractDomain.CPO): sig 
  include AbstractDomain.CPO with type t = X.t * Y.t
end