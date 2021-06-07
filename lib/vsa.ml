open Core_kernel
open Bap.Std

module VsaDom = ProductDomain.BottomReduction(ImmEnv.BooleanImmediates)(ValueStore.AbstractStore)

let is_bool (v: Var.t) = Var.typ v |> function 
  | Type.Imm x -> Int.equal x 1 
  | _ -> false


  (* goal here is to return both an overapproximation of true and overapproximation of false... i think this should be calculable
  any non boolean thing should be pulled from normal denotation. Could sparse up the repr by only considering variables that will be needed later, some sort of backwards slicing on bools.
  
  Ok so a boolean expression is essentially:

  | Predicate:
      | Var_bool
      | NumericExpr Comparison NumericExpr
  | Logical Connective:
    | Predicate AND Predicate
    | Predicate OR Predicate


    The only tricky thing here is numeric exprs. Best precision would be to symbolically solve for each variable in the constraint
    For now let's support two forms of constraints:
    Var Comp Const
    Var Comp Var

    strictly speaking for more precision we would need to solve for each 
    *)

module BoolDom = ProductDomain.MakeProduct(ValueStore.AbstractStore)(ValueStore.AbstractStore)






let binop_to_comp  (comp: binop) = match comp with 
  | EQ -> `EQ
  | NEQ -> `NEQ
  | LT -> `LT
  | LE -> `LE
  | SLT -> `SLT
  | SLE -> `SLE
  | _ -> raise (Failure "not a comparison operator")


let neg_of_comp = function
  | `EQ -> `NEQ
  | `NEQ -> `EQ
  | `LT -> `GE
  | `LE -> `GT
  | `SLT -> `SGE
  | `SLE -> `SGT
  | `GE -> `LT
  | `GT -> `LE
  | `SGE -> `SLT 
  | `SGT -> `SLE


  let get_comp_fun = function 
    | `EQ -> CircularLinearProgression.intersection
    | `NEQ -> raise (Failure "need to implement set difference")
    | `LT -> CircularLinearProgression.limit_lt_unsigned
    | `LE -> CircularLinearProgression.limit_lte_unsigned
    | `SLT -> CircularLinearProgression.limit_lt_signed
    | `SLE -> CircularLinearProgression.limit_lte_signed
    | `GE -> CircularLinearProgression.limit_gte_unsigned
    | `GT -> CircularLinearProgression.limit_gt_unsigned
    | `SGE -> CircularLinearProgression.limit_gte_signed
    | `SGT -> CircularLinearProgression.limit_gt_signed

let denote_comp with_op to_limit with_val = let op_fun = ValueStore.ValueSet.pairwise_function_inclusive ~f:(get_comp_fun with_op) in op_fun to_limit with_val

let constrain_var (v: var) (curr_store: ValueStore.AbstractStore.t) with_op (with_val: ValueStore.ValueSet.t) =
    let v_val = ValueStore.AbstractStore.get curr_store (ValueStore.ALoc.Var v) in 
   ValueStore.ALoc.Map.set curr_store ~key:(ValueStore.ALoc.Var v) ~data:(denote_comp with_op v_val with_val)
    


let flip_comp = function 
| `EQ -> `EQ
| `NEQ -> `NEQ
| `LT -> `GT
| `LE -> `GE
| `SLT -> `SGT
| `SLE -> `SGE
| `GE-> `LE
| `GT -> `LT
| `SGE -> `SLE
| `SGT ->  `SLT




let limit_var lv vs with_op (with_val: word) = 
  constrain_var lv vs with_op (ValueStore.ValueSet.abstract_constant with_val)


let limit_two_vars comp lv rv vs =   let constrained_by_left = constrain_var lv vs comp (ValueStore.AbstractStore.get vs (ValueStore.ALoc.Var rv)) in
let constrained_by_right = constrain_var rv constrained_by_left (flip_comp comp) (ValueStore.AbstractStore.get vs (ValueStore.ALoc.Var rv))
in constrained_by_right



let handle_predicate (comp: binop) (lh: exp) (rh: exp) (vs: ValueStore.AbstractStore.t): BoolDom.t =
  let comp = binop_to_comp comp in   
  match (lh,rh) with 
  | (Bil.Var lv, Bil.Var rv) -> (
  limit_two_vars comp lv rv vs,limit_two_vars (neg_of_comp comp) lv rv vs)
  | (Bil.Var lv, Bil.Int ri) -> (limit_var lv vs comp ri , limit_var lv vs (neg_of_comp comp) ri)
  | (Bil.Int li, Bil.Var rv) ->
    let flipped = flip_comp comp in 
    
    (limit_var rv vs flipped li, limit_var rv vs (neg_of_comp flipped) li)
  | _ -> (vs,vs)

let rec denote_exp_as_bool (e: Exp.t) (pred: VsaDom.t): BoolDom.t =
  let (imms,vs) = pred in 
  match e with 
    | Bil.Var x -> Option.value  ~default:(ValueStore.AbstractStore.bot, ValueStore.AbstractStore.bot) (Var.Map.find imms x)
    | Bil.Int x -> if Word.equal (Word.one 1) x then  (vs, ValueStore.AbstractStore.bot) else  (ValueStore.AbstractStore.bot, vs)
    | Bil.BinOp (op,l,r) -> 
      (match op with 
        | AND | OR -> 
          let (tl, fl) = denote_exp_as_bool l pred in
          let (tr, fr) = denote_exp_as_bool r pred in 
            (match op with
              | AND -> (ValueStore.AbstractStore.meet tl tr,ValueStore.AbstractStore.join fl fr) (* i think the meets should be safe given that all values are computed from pred*)
              | OR -> (ValueStore.AbstractStore.join tl tr,ValueStore.AbstractStore.meet fl fr)
              | _ -> raise (Failure "impossible"))

        | EQ | NEQ |LT | LE |SLT |SLE -> handle_predicate op l r vs
        | _ -> (*welp we are screwed for now so*) (vs,vs))
    |_ -> (vs,vs)
            
let denote_bin_op (op: binop) (s1: ValueStore.ValueSet.t) (s2: ValueStore.ValueSet.t):  ValueStore.ValueSet.t  =
  let f = match op with 
      | PLUS -> CircularLinearProgression.add 
      | MINUS -> CircularLinearProgression.sub
      | TIMES -> CircularLinearProgression.unsigned_mul 
      | DIVIDE -> CircularLinearProgression.unsigned_div
      | SDIVIDE -> CircularLinearProgression.signed_div
      | MOD -> CircularLinearProgression.unsigned_modulo
      | SMOD -> CircularLinearProgression.signed_modulo
      | RSHIFT -> CircularLinearProgression.right_shift_unsigned
      | ARSHIFT -> CircularLinearProgression.right_shift_signed
      | AND -> CircularLinearProgression.logand
      | OR -> CircularLinearProgression.logor
      | XOR -> CircularLinearProgression.logxor
      | EQ -> CircularLinearProgression.equality
      | NEQ -> CircularLinearProgression.not_equal
      | LT -> CircularLinearProgression.less_than_unsigned
      | LE -> CircularLinearProgression.lte_unsigned
      | SLT -> CircularLinearProgression.less_than_signed
      | SLE -> CircularLinearProgression.lte_signed
      | LSHIFT -> CircularLinearProgression.left_shift
    in 
    ValueStore.ValueSet.pairwise_function_inclusive ~f:f s1 s2

let denote_un_op (op: unop) (s: ValueStore.ValueSet.t): ValueStore.ValueSet.t = let f = match op with 
  | NEG -> CircularLinearProgression.neg
  | NOT -> CircularLinearProgression.not_clp
  in
    ValueStore.ValueSet.apply_function ~f:f s



let exec_cast_on (ctype: cast) (v: ValueStore.ValueSet.t) (target_width: int) = let f = match ctype with 
  | UNSIGNED -> CircularLinearProgression.zero_extend ~width:target_width
  | SIGNED -> CircularLinearProgression.sign_extend ~width:target_width
  | HIGH ->  CircularLinearProgression.shrink_high ~width:target_width (*narrow keeping high bit*)
  | LOW ->  CircularLinearProgression.shrink_low ~width:target_width (*narrow keeping low bits*)
in
ValueStore.ValueSet.apply_function ~f:f v

let contains_no_heap_objects (access_list: ValueStore.ALoc.t list) = 
  not (List.exists 
  
  ~f:(function  
    | Var _ -> false
    | Mem (Heap _,_) -> true
    | Mem _ -> false)  access_list)

let contains_no_recursive_objects (access_list: ValueStore.ALoc.t list) (non_rec_procs: Tid.Set.t) = 
  List.for_all ~f:(function 
  | Var _ -> true
  | Mem (Heap _, _) -> true
  | Mem (Stack t,_) -> Tid.Set.mem non_rec_procs t
  | Mem (Global,_) -> true 
  ) access_list

let can_strong_update (fully_accssed: ValueStore.ALoc.t list) (partially_accesed: ValueStore.ALoc.t list) ((_,non_rec_procs): ValueStore.ALocMap.t) = 
  List.is_empty partially_accesed && List.length fully_accssed = 1 && contains_no_heap_objects fully_accssed && contains_no_recursive_objects fully_accssed non_rec_procs


let denote_load (mp: ValueStore.ALocMap.t) (pred: ValueStore.AbstractStore.t) (addr_res: ValueStore.ValueSet.t) (endianess: endian) (sz: Size.all) = 
  let (f,p) = ValueStore.ALocMap.deref mp addr_res (Size.size_in_bytes sz) in
    if List.is_empty p then 
      List.map ~f:(ValueStore.AbstractStore.get pred) f |> List.reduce_exn ~f:ValueStore.ValueSet.join
    else 
      ValueStore.ValueSet.top

let rec denote_value_exp (first_exp: Exp.t) (vsa_dom: VsaDom.t) (mp: ValueStore.ALocMap.t): ValueStore.ValueSet.t = 
  let (immenv, pred) = vsa_dom in 
  match first_exp with 
   | Int w -> ValueStore.ValueSet.abstract_constant w
   | Var v -> ValueStore.AbstractStore.get  pred (ValueStore.ALoc.Var v)
   | Let (v,e1,e2) ->
    if is_bool v then 
      let bs = denote_exp_as_bool e1 vsa_dom in 
        let new_imenv = Var.Map.set immenv ~key:v ~data:bs in denote_value_exp e2 (new_imenv,pred) mp
    else
      let new_bindings = ValueStore.ALoc.Map.set pred ~key:(ValueStore.ALoc.Var v) ~data:(denote_value_exp e1 vsa_dom mp) in denote_value_exp e2 (immenv,new_bindings) mp
   | BinOp (op, e1, e2) -> denote_bin_op op (denote_value_exp e1 vsa_dom mp) (denote_value_exp e2 vsa_dom mp)
   | UnOp (op, e) -> denote_un_op op (denote_value_exp e vsa_dom mp)
   | Ite (b, th, el) -> let (tres,fres) = denote_exp_as_bool b vsa_dom in ValueStore.ValueSet.join (denote_value_exp th (immenv,tres) mp)  (denote_value_exp el (immenv,fres) mp)
   | Cast (cast_ty, width, e) -> let evaluated = denote_value_exp e vsa_dom mp in exec_cast_on cast_ty evaluated width
   | Unknown _ -> raise (Failure "something failed to lift")
   | Extract (lower, upper,e) -> let res = denote_value_exp e vsa_dom mp in ValueStore.ValueSet.apply_function ~f:(CircularLinearProgression.extract lower upper) res
   | Concat (e1,e2) -> let e1 = denote_value_exp e1 vsa_dom mp in let e2 = denote_value_exp e2 vsa_dom mp in ValueStore.ValueSet.pairwise_function_inclusive ~f:CircularLinearProgression.concat e1 e2
   | Load (_,addr, endianess, sz) -> let evaluted_addr = denote_value_exp addr vsa_dom mp in denote_load mp pred evaluted_addr endianess sz


let denote_def  (d: Def.t) (pred: VsaDom.t): VsaDom.t = 
  let assignee  = Def.lhs d in
  let (imms, vs) = pred in 
  if is_bool assignee then  
    (Var.Map.set imms ~key:assignee
    ~data:(denote_exp_as_bool (Def.rhs d) pred) , vs)
  else
  (*if we arent updating a boolean *)
  let denote_def' (pred : ValueStore.AbstractStore.t): ValueStore.AbstractStore.t = 
    raise (Failure "unimplemented")
in (Var.Map.map imms ~f:(fun (t,f) -> denote_def' t,  denote_def' f) , denote_def' vs)
