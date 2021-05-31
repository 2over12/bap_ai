(*
open Bap.Std
open Core_kernel


module Key = struct
  type point = addr
  type t = {lo: word; hi: word} [@@deriving compare, sexp]

  let lower a = a.lo
  let upper a = a.hi
  
  let compare_point = Word.compare

  let sexp_of_point = Word.sexp_of_t


end


module IT = Interval_tree.Make(Key)


module Mem: sig 
  include AbstractDomain.CPO
end 
= struct 

  module T = struct
    type t = ClpDomain.t IT.t

    let sexp_of_t = IT.sexp_of_t ClpDomain.sexp_of_t
    let compare = raise (Failure "havent implemented compare")
    let t_of_sexp = raise (Failure "no parsing")
  end

  include Comparable.Make(T)
  
end

module CPO = MapDomain.MakeMap(Var)(Mem)

*)