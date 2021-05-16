module type CPO = sig 
    include AbstractDomain.CPO
  end
  


module MakeMap(X: AbstractDomain.SET)(Y: AbstractDomain.CPO): CPO