module MakeMap(X: AbstractDomain.SET)(Y: AbstractDomain.CPO): sig 
    include AbstractDomain.CPO with type t = Y.t X.Map.t
end