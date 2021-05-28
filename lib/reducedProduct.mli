module type CPO = sig 
    include AbstractDomain.CPO
end
 
module MakeProduct(X: AbstractDomain.CPO)(Y: AbstractDomain.CPO): CPO

