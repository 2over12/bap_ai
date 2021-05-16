open Core_kernel
open Bap.Std
module W = Word


module T = struct 
type t =  {
  base: Z.t;
  step: Z.t; 
  card: Z.t;
  width: int
} [@@deriving compare]

  let sexp_of_t (v:t)  = Sexp.List [Sexp.Atom (Z.to_string v.base); Sexp.Atom (Z.to_string v.step); Sexp.Atom (Z.to_string v.card); Sexp.Atom (Int.to_string v.width)]
  let t_of_sexp (v:Sexp.t) = raise (Failure "") (* TODO parse the thing*)
end

include T
include Comparable.Make(T)
let comp_size_with_modifier (c:t) (modif: int) = (Z.pow  (Z.succ Z.one) (c.width+ modif))

let comp_size (c: t) = comp_size_with_modifier c 0

let comp_k (c: t) = if Z.equal c.step Z.zero then Z.one else Z.div (Z.lcm (Z.abs c.step) (comp_size c)) (Z.abs c.step)

let create ~width:(width:int) ~step:(step:Z.t) ~card:(card:Z.t) (base:Z.t) = {width=width;step=step; base=base;card=card} 


let min_uelem (c: t) gap_size = Z.erem (Z.erem c.base gap_size) (comp_size c)


(*
Ok so the goal here is to compute i_b first we find x s.t.

x+c*k=i_b

this is true because k = lcm(2^w,s)/s so k=(s * 2^w)/(gcd(s,2^w)*s)

so k=2^w/gcd(2^w,s)

which is the coeffecient for y in the identity gcd(s,2^w)=xs+(2^w)y

by bezout identity we can shift the solution of x by 2^w/gcd(2^w,s) (compensated for by a shift of s/gcd(2^w,s) in the other direction)

once we know x we need to find c such that 0<i_b<n

this means -(x/k)<c<(n-x)/k

the difference between these values is n/(n+1) thus the space in which c can be is always less than 1

this means it must always be the case that c=ceil(-x/k) since c must be an integer and must exist

by eq 6.2 the elements with gab alpha+beta (the big gap) must be greater than or equal to n-ib. We also know for this case there is one such element that satisfies this property
so first_elem = n-ib 
*)

let get_first_elem (cl:t) =
let cl_size = comp_size cl in
let(_,x_for_ia,_) =  Z.gcdext cl.step cl_size in 
(* since we want the solution for -si = gcd(s,y) and we just got the solution for si=gcd(s,y) we need to invert*)
let x = Z.neg x_for_ia in
let k =  (comp_k cl) in 
let c = Z.cdiv (Z.neg x) k in 
let ib = Z.add x (Z.mul c k) in 
let new_basei = Z.sub cl.card ib in 
  Z.erem (Z.add cl.base (Z.mul cl.step new_basei)) cl_size


let compute_last_val (c:t) = Z.erem (Z.add c.base (Z.mul c.step (Z.sub c.card Z.one))) (comp_size c)

let canonize (c: t) =
  let k = comp_k c in
  let gap = Z.gcd c.step (comp_size c) in
  match c.card with
    | z when Z.equal z Z.zero-> {base=Z.zero;step=Z.zero;card=Z.zero;width=c.width}
    | z when Z.equal z Z.one -> {base=(Z.erem c.base (comp_size c));step=Z.zero;card=Z.one;width=c.width}
    | z when Z.leq k c.card && Z.leq (Z.succ Z.one) k -> 
      {base=min_uelem c gap;step=gap;card=k;width=c.width}

    | z when Z.equal c.card (Z.sub k Z.one) && Z.geq c.card (Z.succ Z.one)  -> {width=c.width;step=gap;card=c.card;base=get_first_elem c}
    | _ -> let sz = (comp_size c) in 
           let s' = Z.erem c.step sz in if Z.lt s' (comp_size_with_modifier c (-1)) 
            then {base=Z.erem c.base sz;step=s';card=c.card;width=c.width} 
          else 
            let neg_strid = Z.sub sz s' in 
            let last_val = compute_last_val c in {width=c.width;step=neg_strid;card=c.card;base=last_val}