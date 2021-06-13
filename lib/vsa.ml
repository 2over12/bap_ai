open Core_kernel
open Bap.Std
open Bap_core_theory
open Bap_knowledge

open Knowledge.Syntax

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


  (* TODO handle endianess*)
let denote_load (mp: ValueStore.ALocMap.t) (pred: ValueStore.AbstractStore.t) (addr_res: ValueStore.ValueSet.t) (_endianess: endian) (sz: Size.all) = 
  let (f,p) = ValueStore.ALocMap.deref mp addr_res (Size.size_in_bytes sz) in
    if List.is_empty p then 
      List.map ~f:(ValueStore.AbstractStore.get pred) f |> List.reduce_exn ~f:ValueStore.ValueSet.join
    else 
      ValueStore.ValueSet.top
    
let denote_store  (mp: ValueStore.ALocMap.t) (pred: ValueStore.AbstractStore.t) (addr_res: ValueStore.ValueSet.t) (value_res: ValueStore.ValueSet.t) (_endianess: endian) (sz: Size.all) = 
      let (f,p) =  ValueStore.ALocMap.deref mp addr_res (Size.size_in_bytes sz) in
      let should_strong = can_strong_update f p mp in 
      let handled_faccess = List.fold ~init:pred ~f:(fun store aloc  -> let new_data = if should_strong then value_res else 
          let previous_value = ValueStore.AbstractStore.get pred aloc in ValueStore.ValueSet.join previous_value value_res
        in ValueStore.ALoc.Map.set store ~key:aloc ~data:new_data
          ) f in 
      List.fold ~init:handled_faccess ~f:(fun store aloc -> ValueStore.ALoc.Map.set store ~key:aloc ~data:ValueStore.ValueSet.top) p
      



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
   | Store (_mem, _addr, _value, _endianess, _sz) ->  raise (Failure "store is not a value expression")

type evaluated_expr = 
      | Value of ValueStore.ValueSet.t
      | NewEnv of ValueStore.AbstractStore.t 

let denote_expr (first_exp: Exp.t) (vsa_dom: VsaDom.t) (mp: ValueStore.ALocMap.t): evaluated_expr = 
  let (immenv, pred) = vsa_dom in 
  match first_exp with 
    | Store  (_mem, addr, value, endianess, sz)  -> let evaluated_addr = denote_value_exp addr vsa_dom mp in let evaluated_value = denote_value_exp value vsa_dom mp in NewEnv (denote_store mp pred evaluated_addr evaluated_value endianess sz)
    | _ -> Value (denote_value_exp first_exp vsa_dom mp)

let denote_def  (d: Def.t) (pred: VsaDom.t) (mp: ValueStore.ALocMap.t): VsaDom.t = 
  let assignee  = Def.lhs d in
  let (imms, vs) = pred in 
  if is_bool assignee then  
    (Var.Map.set imms ~key:assignee
    ~data:(denote_exp_as_bool (Def.rhs d) pred) , vs)
  else
  (*if we arent updating a boolean *)
  let denote_def' (pred : ValueStore.AbstractStore.t): ValueStore.AbstractStore.t = 
    let res_of_expr = denote_expr (Def.rhs d) (imms,pred) mp in 
    match res_of_expr with 
      | Value nval -> ValueStore.ALoc.Map.set pred ~key:(ValueStore.ALoc.Var assignee) ~data:nval
      | NewEnv updated_store -> updated_store
in (Var.Map.map imms ~f:(fun (t,f) -> denote_def' t,  denote_def' f) , denote_def' vs)


type jmp_results = {successors: tid list; take_jmp: VsaDom.t; dont_take: VsaDom.t}

let apply_guard (pred: VsaDom.t) (value) = raise (Failure "not implemented")

let denote_jmp (jmp : Jmp.t) (pred: VsaDom.t): jmp_results = raise (Failure "not implemented")
let denote_block (blk: Blk.t) (pred: VsaDom.t) (mp: ValueStore.ALocMap.t): VsaDom.t = 
  let phi_nodes = Term.enum phi_t blk in 
  assert (Seq.is_empty phi_nodes);

  let defs = Term.enum def_t blk in 


  let before_jumps = Seq.fold ~init:pred ~f:(fun new_pred df ->
      
      denote_def df new_pred mp ) defs in

  let jmps = Term.enum jmp_t blk in 
    raise (Failure "not implemented") 



(*TODO hmm didnt require GT*)


module CPOToBAPDom(X: AbstractDomain.CPO)(Y: sig 
  val name: string
end) = struct 
  let order x y = if (X.eq x y) then 
    KB.Order.EQ
  else if (X.le x y) then 
    KB.Order.LT
  else 
    KB.Order.NC

  let dom = KB.Domain.define ~join:(fun x y -> Result.Ok (X.join x y)) ~empty:X.bot ~order:order Y.name
end


type KB.conflict += | FlatDomain 

module FlatDomain(T: T)(Y: sig 
  val name: string
end) = struct 
  type t = T.t Option.t


  let order x y = match (x,y) with 
    None, None | Some _, Some _-> KB.Order.NC
    | Some _ , None -> KB.Order.GT
    | None, Some _ -> KB.Order.LT

    let dom = KB.Domain.define ~join:(fun x y -> match (x,y) with
    | None, None -> Result.Ok None
    | Some _, Some _ -> Result.Error FlatDomain
    | Some x, None -> Result.Ok (Some x)
    | None, Some y -> Result.Ok (Some y)
  ) ~empty:None ~order:order Y.name


  
end

module ValueSetDom = CPOToBAPDom(ValueStore.ValueSet)(struct let name = "valueset" end)
module AbstractStoreDom = CPOToBAPDom(ValueStore.AbstractStore)(struct let name = "abstractstore" end)

module VsaKBDom = CPOToBAPDom(VsaDom)(struct let name = "vsadom" end)

module ProduceVsaDom = FlatDomain(struct 
type t = VsaDom.t -> VsaDom.t
end)(struct let name = "compute_abstractstore" end)


module ProduceVsaDom = FlatDomain(struct 
type t = VsaDom.t -> BoolDom.t
end)(struct let name = "compute_bool_dom" end)


module ProduceValueSet = FlatDomain(struct 
  type t = ValueStore.AbstractStore.t -> ValueStore.ValueSet.t
end)(struct let name = "compute_valueset" end)



module ProduceBoolean = FlatDomain(struct 
  type t = VsaDom.t -> BoolDom.t
end)(struct let name = "compute_valueset" end)

let preds_set = KB.Domain.powerset (module Tid) "prececessors"


let post_conds = KB.Domain.mapping

let valueset_map ~f:(f:ValueStore.ValueSet.t -> ValueStore.ValueSet.t) (x: ProduceValueSet.t) = Option.map ~f:(fun producer -> fun ctxt -> f (producer ctxt)) x


let compute_exp_slot = KB.Class.property ~package:"bap_ai" Theory.Value.cls  ~public:true "exp_value" ProduceValueSet.dom

let compute_bool_slot = KB.Class.property ~package:"bap_ai" Theory.Value.cls ~public:true "exp_bool_value" ProduceBoolean.dom

let compute_post_condidtion = KB.Class.property ~package:"bap_ai" Theory.Effect.cls ~public:true "stmt_value" ProduceVsaDom.dom

let prec_slot = KB.Class.property ~package:"bap_ai" Theory.Program.cls ~public:true "precondition" VsaKBDom.dom


module Bitv = struct 

end 


module GrabValues : Theory.Core = struct 
  include Theory.Empty

(*
  let blk (lbl: Tid.t) (statements: Theory.data Theory.eff) (jmps: Theory.ctrl Theory.eff) = KB.collect prec_slot lbl >>= fun precond ->
  *)  
     
     (*statements >>= fun stats -> ((KB.Value.get compute_post_condidtion stats):ProduceAbstractStore.t)*)
end




module SolvableBooleanExpressions: Theory.Core = struct end

module Denotation: Theory.Core = struct
  include Theory.Empty
  

  let value x = KB.Value.get compute_exp_slot x

  let (>-->) (x: 's Theory.bitv) (f: ValueStore.ValueSet.t -> ValueStore.ValueSet.t) =  x >>| (fun v -> 
    let maybe_vs_computer = KB.Value.get compute_exp_slot v in
    let new_vs = Option.map ~f:(fun vs_computer -> 
      fun state -> f (vs_computer state)
      ) maybe_vs_computer in
    let nval =  KB.Value.put compute_exp_slot v new_vs in
    nval)

  let lift f: ('s Theory.bitv -> 's Theory.bitv) = fun x -> (x >--> f)

  let unop f: ('s Theory.bitv -> 's Theory.bitv)   = fun x -> lift f x

  let unop_app ~f = unop (ValueStore.ValueSet.apply_function ~f:f)
  let not x = unop_app  ~f:CircularLinearProgression.not_clp x

  let neg x = unop_app  ~f:CircularLinearProgression.neg x


 
  let append (cst: 'a Theory.Bitv.t Theory.Value.sort) (bv1: 'b Theory.bitv) (bv2: 'c Theory.bitv) = bv1 >>= fun bv1 -> (bv2 >>= fun bv2 -> 
      let b1s = Theory.Value.sort bv1 in 
      let b2s = Theory.Value.sort bv2 in
      let bv1_size  =  Theory.Bitv.size b1s in
      let bv2_size = Theory.Bitv.size b2s in 
      let app_size = bv1_size + bv2_size in 
      let goal = Theory.Bitv.size cst in 
    
      let appended: (ProduceValueSet.t) = 
        Option.map2 ~f:(fun bv1_f bv2_f -> fun ctxt -> ValueStore.ValueSet.pairwise_function_inclusive ~f:(CircularLinearProgression.concat) (bv1_f ctxt) (bv2_f ctxt) ) (value bv1) (value bv2)
         in 
      let casted = 
        if app_size = goal then 
          appended 
      else if app_size < goal  
        then
          valueset_map ~f:(fun vset -> exec_cast_on UNSIGNED vset goal) appended
        else
          valueset_map ~f:(fun vset -> exec_cast_on LOW vset goal) appended
      in
       KB.return (KB.Value.put compute_exp_slot (Theory.Value.empty cst) casted)
    )


  
end 
