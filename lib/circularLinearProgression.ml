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

 
 let estimate_number_of_alps (c: canon t) = Z.cdiv (Z.mul c.step c.card) (comp_size c)

 let visit_number_circle (c: canon t) (starting_index: Z.t) = 
  let facts = compute_gap_width c in 
  let rec run_visit curr_ind n  _ = if Z.geq n c.card then OSeq.Nil else OSeq.Cons (curr_ind, run_visit (succ c facts curr_ind) (Z.succ n)) in run_visit starting_index Z.zero


(* groups should be such that the gap lengths to pred are equal and the two points do not cross the wrapping point*)


let get_succesor_gap_length (c:canon t) (gap_info: computed_clp_facts) (i: Z.t) =
  if (Z.lt i (Z.sub c.card gap_info.ia)) then gap_info.alpha
  else if (Z.leq gap_info.ib i) then gap_info.beta else
    Z.add gap_info.beta gap_info.alpha

let get_pred_gap_length (c:canon t) (gap_info: computed_clp_facts) (i: Z.t) = 
    if Z.lt i (Z.sub c.card gap_info.ib) then gap_info.beta else
      if Z.leq gap_info.ia i then gap_info.alpha else 
        Z.add gap_info.beta gap_info.alpha

let group_consecutive (gap_info: computed_clp_facts) (c: canon t) (seq: Z.t OSeq.t) = 
  let rec grouper (sub_seq: Z.t OSeq.t) () = 
    match sub_seq () with 
      | OSeq.Nil -> OSeq.Nil 
      | OSeq.Cons (x,rst) -> let xlen = get_succesor_gap_length c gap_info x in
        let matching_items i = Z.equal (get_pred_gap_length c gap_info i ) xlen in
       let group = OSeq.cons x (OSeq.take_while matching_items rst) in 
       OSeq.Cons (group,(grouper (OSeq.drop_while matching_items rst)))
    in grouper seq



  let rec take_big_int (i: Z.t) (seq: 'a OSeq.t) () = 
    if Z.leq i Z.zero then OSeq.Nil else 
      let curr_node = seq () in 
          match curr_node with 
            OSeq.Nil -> OSeq.Nil
          | OSeq.Cons (x,rst) -> OSeq.Cons (x, take_big_int (Z.pred i) rst)


  let slow_alps_strategy  (c: canon t) (wrapping_point: Z.t) (index_to_value: canon t -> Z.t -> Z.t) (alp_limit: Z.t) = 
    let (gap_info, (ic,zeta)) = compute_gap_width_ex c wrapping_point in 
    (* we start our visit from the index immediately after the wrapping point so that we never have to wrap*)
    let ind_seq = visit_number_circle c ic in
    let alp_groups = group_consecutive gap_info c ind_seq in
    let limited_groups = take_big_int alp_limit alp_groups in
    let make_alp_from_group (grp: Z.t OSeq.t) = 
      let grp_lst = OSeq.to_list grp in 
      let base_index = List.hd_exn grp_lst in 
      let card = List.length grp_lst |> Z.of_int in (*todo the list could be too long*)
      let step = get_succesor_gap_length c gap_info base_index in 
        ({step=step;card=card;width=c.width; base=index_to_value c base_index}: alp t) in
    let all_alps = OSeq.map make_alp_from_group limited_groups in 
    let total_card = OSeq.fold (fun acc current_alp -> Z.add acc (current_alp.card)) Z.zero all_alps in 
      if Z.equal total_card c.card then Some all_alps else None
  


let get_alps  (c:canon t) (wrapping_point: Z.t) index_to_value =
      let alp_limit = estimate_number_of_alps c in
      let slow_alps = slow_alps_strategy c wrapping_point index_to_value alp_limit in
      match slow_alps with 
        None -> split_clp_by c wrapping_point index_to_value
        | Some a -> OSeq.to_list a

let signed_alps (c:canon t) =  
  let wval = comp_size_with_modifier c (-1) |> Z.pred in 
get_alps c wval compute_signed_index_value


let unsigned_alps (c:canon t) = let sz = Z.pred (comp_size c) in 
 get_alps c sz compute_index_value


let bottom ~width = create ~width:width ~step:Z.zero ~card:Z.zero Z.zero

let is_bottom (x: canon t) = equal (bottom ~width:x.width) x

let u'_card b s c1 c2 = (Z.fdiv (Z.sub (Z.max (compute_index_value c1 (Z.pred c1.card) ) 
  (compute_index_value c2 (Z.pred c2.card) )) b) s)

let u' (c1: canon t) (c2: canon t)= let b = Z.min c1.base c2.base in 
  let s = Z.gcd c1.step c2.step |> Z.gcd (Z.sub c1.base c2.base|> Z.abs) in 
  let n = u'_card b s c1 c2 in create ~width:c1.width ~step:s ~card:n b

 let union (x: canon t) (y: canon t) = 
    if equal x y then x else
    if is_bottom x then y else 
    if is_bottom y then x else
    if Z.equal x.card Z.one && Z.equal y.card Z.one then 
      create ~width:x.width ~card:(Z.succ Z.one) ~step:(Z.abs (Z.sub x.base y.base)) (Z.min x.base y.base)
  else
    (* the argmin value isn tclear to me *)
    u' x y


let min_u (c1: canon t) = let (_,(i,_)) = compute_gap_width_ex c1 Z.zero in i

let closest_less_than_n (c1: canon t) (n: Z.t) = let  (facts,(min_i,_)) =  compute_gap_width_ex c1 n in pred c1 facts min_i

let max_u (c1: canon t) = closest_less_than_n c1 Z.zero

let concretize (index_to_value: 'a t -> Z.t -> Z.t)  (c1: 'a t) = 
  let rec concretize' n = if Z.equal c1.card n then [] else let curr_val = index_to_value c1 n in curr_val :: (concretize' (Z.succ n)) 
    in concretize' Z.zero

let unsigned_concretize = concretize compute_index_value

let intersection (c1: canon t) (c2: canon t) = if is_bottom c1 && is_bottom c2 then bottom ~width:c1.width else
  let sz =  (comp_size c1) in 
  let (d,s,_) = Z.gcdext c1.step sz in 
  let (e,t,_) = Z.gcdext c2.step d in
  let j_0 = Z.erem (Z.div (Z.mul t (Z.sub c1.base c2.base)) e) (Z.div d e) in
  let i_base = Z.div (Z.mul s (Z.add (Z.sub c2.base c1.base) (Z.mul c2.step j_0))) d in
  let i_step = Z.div (Z.mul c2.step s) e in 
  let i_card = Z.fdiv (Z.sub c2.card j_0) (Z.div d e) in 
  let cap_I = create ~width:(Z.log2 (Z.div sz d)) ~card:i_card ~step:i_step i_base in 
  let i_0 = min_u cap_I |> compute_index_value cap_I in
  let i_1 = closest_less_than_n c1 c1.card |>  compute_index_value cap_I in 
    if not (Z.divisible (Z.sub c1.base c2.base) e) || Z.geq j_0 c2.card || Z.geq i_0 c1.card then bottom ~width:c1.width else 
      let b = compute_index_value c1 i_0 in 
      let total_values = unsigned_concretize cap_I in (* TODO this cant be what they mean*)
      let lh = List.filter ~f:(fun v -> Z.geq v i_0) total_values in
      let rh = List.filter ~f:(fun v -> Z.leq v i_1) total_values in
      let prod = List.cartesian_product lh rh in 
      let diffs = List.map ~f:(fun (f,s) -> Z.sub f s|> Z.abs) prod in 
      let gcd_factor = List.reduce_exn ~f:Z.gcd diffs in
      let s = Z.mul c1.step gcd_factor in 
      let n = Z.fdiv (Z.sub (compute_index_value c1 i_1) (compute_index_value c1 i_0)) s  |> Z.succ in 
        create ~width:c1.width ~card:n ~step:s b

let subset_of (c1: canon t) (c2: canon t) = 
    (is_bottom c1 && is_bottom c2) || (not (Z.gt c1.card c2.card) && 
    let sz = comp_size c1 in 
    let (d,s,_) = Z.gcdext c2.step sz in 
    let cap_J = create ~width:(Z.log2 (Z.div sz d)) ~card:c1.card ~step:(Z.div (Z.mul s c1.step) d) (Z.div (Z.mul s (Z.sub c1.base c2.base)) d) in
    let j_1 = max_u cap_J in 
    (Z.divisible (Z.sub c1.base c2.base) d) && Z.divisible c1.step d && not (Z.geq j_1 c2.card)
    )


let neg (c: canon t) = if is_bottom c then c else create ~width:c.width ~step:c.step ~card:c.card (Z.neg (compute_index_value c (Z.pred c.card)))

let bin_op f (c1: canon t) (c2: canon t) = if is_bottom c1 || is_bottom c2 then bottom ~width:c1.width else f c1 c2

let get_last_value (c: 'a t) = compute_index_value c (Z.pred c.card)

let add = let add' c1 c2 =
  let b = Z.add c1.base c2.base in 
    if Z.equal c1.card Z.one && Z.equal c2.card Z.one then create ~width:c1.width ~step:Z.zero ~card:Z.one b
    else
      let s = Z.gcd c1.step c2.step in 
      let n = Z.fdiv (Z.sub (Z.add (get_last_value c1) (get_last_value c2)) b) s |> Z.succ in
      create ~width:c1.width ~step:s ~card:n b
    in bin_op add'

let sub c1 c2 = add c1 (neg c2)


let bin_op_on_alps splitter f  c1 c2 ~width = let c1_splits = splitter c1 in
      let c2_splits = splitter c2 in
      let combs = List.cartesian_product c1_splits c2_splits |> List.map ~f:f in
      List.fold ~f:union ~init:(bottom ~width:width)
      

let bin_op_on_signed_alps = bin_op_on_alps signed_alps

let bin_op_on_unsigned_alps = bin_op_on_alps unsigned_alps

let bin_op_on_signed_alps_same_width f c1 = bin_op_on_signed_alps f c1 ~width:c1.width

let bin_op_on_unsigned_alps_same_width   f c1 = bin_op_on_unsigned_alps f c1 ~width:c1.width

