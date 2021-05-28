type t = CircularLinearProgression.canon CircularLinearProgression.t

include CircularLinearProgression.T

let join = CircularLinearProgression.union

let meet = CircularLinearProgression.intersection


let sexp_of_t = CircularLinearProgression.sexp_of_t

let t_of_sexp = CircularLinearProgression.t_of_sexp

let eq = CircularLinearProgression.equal

let le = CircularLinearProgression.subset_of

let bot = CircularLinearProgression.bottom ~width:1 

let widen (c1 :t) (c2: t) = raise (Failure "not implemented")

let narrow (c1 :t) (c2: t) = raise (Failure "not implemented")
