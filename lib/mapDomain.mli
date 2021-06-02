module MakeMap(X: AbstractDomain.SET)(Y: AbstractDomain.CPO): sig 
    include AbstractDomain.CPO with type t = Y.t X.Map.t


    val pairwise_function_inclusive: f:(Y.t -> Y.t -> Y.t) ->  Y.t X.Map.t ->  Y.t X.Map.t ->  Y.t X.Map.t

    val get: t -> X.t -> Y.t
end