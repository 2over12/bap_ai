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


module KnownForm = struct
  type connective_op =  
    | AND 
    | OR [@@deriving sexp,compare]

  type predicate_op =
    | EQ
    | NEQ
    | SLT
    | ULT
    | SGT
    | UGT
    | SGE
    | UGE
     [@@deriving sexp,compare]
    

  

  type atom = 
    | Var of var
    | Int of word [@@deriving sexp,compare]
  
  

  type known_exp = 
    | Atom of atom
    | Connective of connective_op * known_exp * known_exp
    | Predicate of predicate_op * atom * atom [@@deriving sexp,compare]
  module T = struct 
    type t = known_exp option [@@deriving sexp,compare]
  end

  include Comparable.Make(T)
  include T


  let create_int (w: Theory.word) (width: int) = Some (Atom (Int (Word.create w width)))

  let create_var (v: 'a Theory.var) = Some (Atom (Var (Var.reify v)))
end

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
  else if (X.le y x) then
    KB.Order.GT
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


module ProduceBoolDom = FlatDomain(struct 
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


let known_form_slot = KB.Class.property ~package:"bap_ai" Theory.Value.cls ~public:false "is_known_form" (KB.Domain.flat ~equal:KnownForm.equal ~empty:None "known_form_exp")


module Bitv = struct 

end 


module GrabValues : Theory.Core = struct 
  include Theory.Empty


(*
  let blk (lbl: Tid.t) (statements: Theory.data Theory.eff) (jmps: Theory.ctrl Theory.eff) = KB.collect prec_slot lbl >>= fun precond ->
  *)  
     
     (*statements >>= fun stats -> ((KB.Value.get compute_post_condidtion stats):ProduceAbstractStore.t)*)
end




(*Ok so the goal here is to flatten out the solvable boolean variables into a slot that we can leverage
This will allow certain boolean expression to be calculated in a solvable way
*)


module GenericTheoryOps(X: sig 
type domain
val target_slot: (Theory.Value.cls,domain) KB.slot

end) = struct 
  let (>>->) v f = v >>= fun v -> f (Theory.Value.sort v) (KB.Value.get X.target_slot v)

  let lift2 mk s f x y =
    x >>-> fun sx x ->
    y >>-> fun sy y ->
    mk (s sx sy) (f x y)

  let lift mk s f x = 
      x >>-> fun sx x -> mk (s sx) (f x)

  let same_sort2 s1 s2 = s1 
  
  let same_sort s1 = s1
  let bool_sort x = Theory.Bool.t

  let bool_sort2 x y = Theory.Bool.t


  let mk_bv (s: 's Theory.Value.sort) (v: X.domain) = KB.Value.put X.target_slot (Theory.Value.empty s) v |> KB.return

  let value x = KB.Value.get X.target_slot x
end

module SolvableBooleanExpressions: Theory.Core = struct 
include Theory.Empty

include GenericTheoryOps(struct
type domain = KnownForm.T.t
let target_slot = known_form_slot
end)



let create_atom (kf: KnownForm.t) sort = KB.Value.put known_form_slot (Theory.Value.empty sort) kf |> KB.return


(* Atomics *)
let int (sort: 's Theory.Bitv.t Theory.Value.sort) (v: Theory.word) =  create_atom (KnownForm.create_int v (Theory.Bitv.size sort)) sort

let var (v: 'a Theory.var) = create_atom (KnownForm.create_var v) (Theory.Var.sort v)

(* Connectives *)
let create_connective (conn: KnownForm.connective_op) (b1: KnownForm.t) (b2: KnownForm.t) = Monads.Std.Monad.Option.Syntax.(
  !$$ (fun b1 b2  -> 
    KnownForm.Connective (conn, b1, b2)) b1 b2 
)

let handle_bool (conn:  KnownForm.connective_op) (x: Theory.bool) (y: Theory.bool) = (lift2 mk_bv same_sort2  (create_connective conn) x y)

let and_ (x: Theory.bool) (y: Theory.bool) = handle_bool AND x y

let or_ x y = handle_bool OR x y


let create_predicate (pred_op: KnownForm.predicate_op) (b1: KnownForm.t) (b2: KnownForm.t) = Monads.Std.Monad.Option.Syntax.(
   b1 >>= (fun b1 -> b2 >>= fun b2 -> match (b1,b2) with
    | (Atom x, Atom y) -> Some (KnownForm.Predicate (pred_op,x,y))
    | _ -> None
   )
)

let handle_predicate pred_op x y = (lift2 mk_bv bool_sort2 (create_predicate pred_op) x y)
(*Predicates*)
let neq (x: 'a Theory.bitv) (y: 'a Theory.bitv) = handle_predicate NEQ x y

let eq (x: 'a Theory.bitv) (y: 'a Theory.bitv) = handle_predicate EQ x y

let slt (x: 'a Theory.bitv) (y: 'a Theory.bitv) = handle_predicate SLT x y

let ult (x: 'a Theory.bitv) (y: 'a Theory.bitv) = handle_predicate ULT x y


let sgt (x: 'a Theory.bitv) (y: 'a Theory.bitv) = handle_predicate SGT x y

let ugt  (x: 'a Theory.bitv) (y: 'a Theory.bitv) = handle_predicate UGT x y



let sge  (x: 'a Theory.bitv) (y: 'a Theory.bitv) = handle_predicate SGE x y

let uge  (x: 'a Theory.bitv) (y: 'a Theory.bitv) = handle_predicate UGE x y

end

module Denotation: Theory.Core = struct
  include Theory.Empty
  include GenericTheoryOps(struct
type domain = ProduceValueSet.t
let target_slot = compute_exp_slot
end)

  

  let unop f x = lift mk_bv same_sort f x
  
  let chain_with ~f:(f:ValueStore.ValueSet.t-> ValueStore.ValueSet.t) (f_orig: ProduceValueSet.t)  = Monads.Std.Monad.Option.Syntax.(
     !$(fun prev -> fun vstore -> f (prev vstore)) f_orig
  )

  let apply_function f x = chain_with ~f:(ValueStore.ValueSet.apply_function ~f:f) x

    
  let unop_app x ~f:(f:ClpDomain.t -> ClpDomain.t) = unop (apply_function f) x

  let not x = unop_app  ~f:CircularLinearProgression.not_clp x

  let neg x = unop_app  ~f:CircularLinearProgression.neg x
 

  let binop f x y = lift2 mk_bv same_sort2 f x y


  let chain2 ~f:(f: ValueStore.ValueSet.t -> ValueStore.ValueSet.t -> ValueStore.ValueSet.t) (forig1: ProduceValueSet.t) (forig2: ProduceValueSet.t) = Monads.Std.Monad.Option.Syntax.(
    !$$ (fun forig1 forig2 -> fun vstore -> f (forig1 vstore) (forig2 vstore)) forig1 forig2)

  let binop_pairwise_inclusive x y ~f:(f:ClpDomain.t -> ClpDomain.t -> ClpDomain.t) = chain2 ~f:(ValueStore.ValueSet.pairwise_function_inclusive ~f:f) x y
 

  let binop_app x y  ~f:(f:ClpDomain.t -> ClpDomain.t -> ClpDomain.t) = binop (binop_pairwise_inclusive ~f:f) x y

  let add (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_app ~f:CircularLinearProgression.add x y 

  let sub (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_app ~f:CircularLinearProgression.sub x y

  let aloc_from_theory  (v: 'a Theory.var) = (ValueStore.ALoc.Var (Var.reify v))

  let var (v: 'a Theory.var) = mk_bv (Theory.Var.sort v) (Some (fun vstore -> ValueStore.AbstractStore.get vstore (aloc_from_theory v)))


  let unk (s: 'a Theory.Value.sort) = mk_bv s (Some (fun _ -> ValueStore.ValueSet.Top))


  let let_ (v: 'a Theory.var) (exp_v: 'a Theory.pure) (body: 'b Theory.pure) = 
    exp_v >>= (fun exp_v ->
      body >>= (fun body ->   mk_bv (Theory.Value.sort body) (let v_func = (value exp_v) in 
        let body_func = (value body) in 
          Monads.Std.Monad.Option.Syntax.(
            !$$ (fun v_func body_func -> fun vstore -> 
              let res = v_func vstore in
              let new_vstore = ValueStore.ALoc.Map.set vstore ~key:(aloc_from_theory v) ~data:res in 
              body_func new_vstore
              ) v_func body_func
          )

      ) 
        
        ))
  

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
