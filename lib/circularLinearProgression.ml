open Core_kernel
open Bap.Std
module W = Word

type canon
type generic
type alp

type 'a t =  {
  base: Z.t;
  step: Z.t; 
  card: Z.t;
  width: int
} [@@deriving compare]

type 'a t' = 'a t
let sexp_of_t (v: 'a t)  = Sexp.List [Sexp.Atom (Z.to_string v.base); Sexp.Atom (Z.to_string v.step); Sexp.Atom (Z.to_string v.card); Sexp.Atom (Int.to_string v.width)]
let t_of_sexp (v:Sexp.t) = raise (Failure "") (* TODO parse the thing*)


include Comparable.Make(struct 
  type t =  canon t' 

  let sexp_of_t = sexp_of_t
  let t_of_sexp = t_of_sexp

  let compare = compare (fun _ _ -> 0)
end)


let comp_size_with_modifier (c: 'a t) (modif: int) = (Z.pow  (Z.succ Z.one) (c.width+ modif))

let comp_size (c: 'a t) = comp_size_with_modifier c 0

let comp_k (c: 'a t) = if Z.equal c.step Z.zero then Z.one else Z.div (Z.lcm (Z.abs c.step) (comp_size c)) (Z.abs c.step)



let min_uelem (c: 'a t) gap_size = Z.erem (Z.erem c.base gap_size) (comp_size c)


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

let get_first_elem (cl:'a t) =
let cl_size = comp_size cl in
let(_,x_for_ia,_) =  Z.gcdext cl.step cl_size in 
(* since we want the solution for -si = gcd(s,y) and we just got the solution for si=gcd(s,y) we need to invert*)
let x = Z.neg x_for_ia in
let k =  (comp_k cl) in 
let c = Z.cdiv (Z.neg x) k in 
let ib = Z.add x (Z.mul c k) in 
let new_basei = Z.sub cl.card ib in 
  Z.erem (Z.add cl.base (Z.mul cl.step new_basei)) cl_size


let compute_last_val (c:'a t) = Z.erem (Z.add c.base (Z.mul c.step (Z.sub c.card Z.one))) (comp_size c)

let canonize (c: 'a t) =
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
            let last_val = compute_last_val c in ({width=c.width;step=neg_strid;card=c.card;base=last_val}: canon t)



let create ~width:(width:int) ~step:(step:Z.t) ~card:(card:Z.t) (base:Z.t) = canonize {width=width;step=step; base=base;card=card}

let num_steps_leq_n n from by = Z.fdiv (Z.sub n from) by

let num_steps_leq_nsub1 n from by = num_steps_leq_n (Z.sub n Z.one) from by

let num_steps_geq0 from step = Z.fdiv from step

let num_steps_gt0 from step = num_steps_geq0 (Z.sub from Z.one)  step

let shrink ind_constraint gap_constraint n i_shrink g_shrink i_by g_by = 
  let k = Z.min (ind_constraint n i_shrink i_by) (gap_constraint g_shrink g_by) in
  let i' = Z.add i_shrink (Z.mul k i_by) in 
  let g' = Z.sub g_shrink (Z.mul k g_by) in 
  (i', g') 

let shrink_to_gap_0 = shrink num_steps_leq_nsub1 num_steps_geq0

let shrink_to_gap_gt0 = shrink num_steps_leq_nsub1 num_steps_gt0




let compute_index_value_without_mod (c: 'a t) i = (Z.add c.base (Z.mul i c.step))

let compute_index_value (c: 'a t) i = let sz = comp_size c in (Z.erem (Z.add c.base (Z.mul i c.step)) sz)

let compute_signed_index_value (c: 'a t) i = let sz = comp_size c in
  let pval =  compute_index_value_without_mod c i in 
  let modded_pos = Z.erem pval sz in 
    if (Z.lt modded_pos (comp_size_with_modifier c (-1))) then modded_pos else
      Z.sub modded_pos sz

 

type computed_clp_facts = {ia:Z.t;alpha:Z.t; ib:Z.t; beta: Z.t}
let sexp_of_clp_facts (v: computed_clp_facts)  = Sexp.List [Sexp.Atom (Z.to_string v.ia); Sexp.Atom (Z.to_string v.ib); Sexp.Atom (Z.to_string v.alpha); Sexp.Atom (Z.to_string v.beta)]
let clp_facts_of_sexp (v:Sexp.t) = raise (Failure "") (* TODO parse the thing*)



let compute_gap_width_ex (c: canon t) (l: Z.t) = 
  let (ia,ib,ic,alpha,beta,zeta) = 
    let sz = comp_size c in 
    let rec compute_gap_width_ex' ia ib ic alpha beta zeta = 
      
      if Z.geq (Z.add ia ib) c.card 
        then 
          (*base case*)
          (ia, ib, ic, alpha, beta, zeta)
        else
          if Z.lt alpha beta then
            let (ic',zeta') = 
              let k' = Z.cdiv (Z.neg (Z.sub zeta beta)) alpha in 
              (* if shifting wont move n past n-1 and shifting will actually move the gap negative*)
              if (Z.leq k' (num_steps_leq_nsub1 c.card (Z.add ib ic) ia)) && 
                Z.lt (Z.add (Z.neg beta) (Z.mul k' alpha)) Z.zero then
                  let nic = Z.add (Z.add ic ib) (Z.mul k' ia) in
                  let nzeta = (Z.add (Z.sub zeta beta) (Z.mul k' alpha)) in 
                  (nic,nzeta)
            else
                (ic,zeta)   
          in
            let (ib',beta') = shrink_to_gap_gt0 c.card ib beta ia alpha in
            compute_gap_width_ex' ia ib' ic' alpha beta' zeta'
          else 
          let (ic', zeta')  = shrink_to_gap_0 c.card ic zeta ib beta in
          let (ia',alpha') = shrink_to_gap_gt0 c.card ia alpha ib beta  in
          compute_gap_width_ex' ia' ib ic' alpha' beta zeta'
        in 
      if Z.equal c.card Z.one 
        then 
          (Z.zero,Z.zero,Z.zero,sz,sz,Z.erem (Z.sub c.base l) sz)
      else 
        let candidate_zeta_ind0 =  (Z.erem (Z.sub c.base l) sz)  in 
        let candidate_zeta_ind1 = (Z.erem (Z.sub (compute_index_value c Z.one) l) sz)in 
        let (ic, zeta) = 
        if Z.lt candidate_zeta_ind0 candidate_zeta_ind1 then 
          (Z.zero,candidate_zeta_ind0)
        else 
          (Z.one, candidate_zeta_ind1)
      in   
  compute_gap_width_ex' Z.one Z.one ic c.step (Z.sub sz c.step) zeta in {ia=ia;ib=ib;alpha=alpha;beta=beta},(ic,zeta)
   
let compute_gap_width (c:canon t) = let (a,_) = compute_gap_width_ex c Z.zero in a 



let pred (c: canon t) (gaps: computed_clp_facts) (i: Z.t) = 
    if Z.lt i (Z.sub c.card gaps.ib) then (Z.add i gaps.ib) else 
      if Z.leq gaps.ia i then (Z.sub i gaps.ia) else
        (Z.add (Z.sub i gaps.ia) gaps.ib)


let succ (c: canon t) (gaps: computed_clp_facts) (i: Z.t) = 
  if Z.lt i (Z.sub c.card gaps.ia) then (Z.add i gaps.ia) else 
    if Z.leq gaps.ib i then (Z.sub i gaps.ib) else
      (Z.sub (Z.add i gaps.ia) gaps.ib)


  (**must be canonical
  *)

  let rec repeat_while f x g = if g x then x :: repeat_while f (f x) g else []
  

  let gap_length_from from_v towi (c: 'a t)  index_to_value = let sz= comp_size c in 
                                              let tow_v = index_to_value c towi  in 
                                              Z.erem (Z.sub tow_v from_v) sz


  let compute_lap (c: canon t) (wrapping_point: Z.t) index_to_value (lap_start_i: Z.t) = 
    let lap_start_v = index_to_value c lap_start_i in 
    let max_step_num = Z.fdiv (Z.sub wrapping_point lap_start_v) c.step in 
    let  lap_end_i = Z.min (Z.sub c.card Z.one) (Z.add lap_start_i max_step_num) in
      ({card=(Z.add (Z.sub lap_end_i lap_start_i) Z.one);width=c.width;base=lap_start_v;step=c.step}:alp t) 

  (**x' is the last valid value before wrapping*)
  let split_clp_by (c:canon t) (x': Z.t) index_to_value = 
      let sz = comp_size c in
      let x = Z.erem x' sz in 
      let (gaps,(ic,zeta)) = compute_gap_width_ex c x in
      let lst_of_start_bounds' = repeat_while (succ c gaps) ic (fun ind -> (Z.leq (gap_length_from x ind c index_to_value) c.step)) in 
      let lst_of_start_bounds = if List.find lst_of_start_bounds' ~f:(fun ind -> Z.equal ind Z.zero) |> Option.is_some then lst_of_start_bounds' else Z.zero::lst_of_start_bounds' in
      List.map ~f:(compute_lap c x index_to_value) lst_of_start_bounds

let signed_alps (c:canon t) = 
  let wval = comp_size_with_modifier c (-1) |> Z.pred in 
  split_clp_by c wval compute_signed_index_value

let unsigned_alps (c:canon t) = let sz = Z.pred (comp_size c) in 
 split_clp_by c sz compute_index_value