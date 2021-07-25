open Core_kernel
open Bap.Std
open Bap_core_theory
open Bap_knowledge

open Knowledge.Syntax
open Knowledge.Let
module VsaDom = ProductDomain.BottomReduction(ImmEnv.BooleanImmediates)(ValueStore.AbstractStore)

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

  
  let calculate_atom (a: atom) (pred: VsaDom.t): BoolDom.t = 
    let (bool_bindings, abstract_store) = pred in 
    match a with 
      | Var v -> Var.Map.find bool_bindings v |> Option.value ~default:(ValueStore.AbstractStore.bot, ValueStore.AbstractStore.bot)
      | Int c -> if Word.equal c (Word.one 1)then (abstract_store, ValueStore.AbstractStore.bot) else (ValueStore.AbstractStore.bot, abstract_store)






let neg_of_comp = function
| `EQ -> `NEQ
| `NEQ -> `EQ
| `SLT -> `SGE
| `ULT -> `UGE
| `SGT -> `SLE
| `UGT -> `ULE
| `SGE -> `SLT
| `UGE -> `ULT
| `SLE -> `SGT
| `ULE -> `UGT

let flip_comp = function 
| `EQ -> `EQ
| `NEQ -> `NEQ
| `SLT -> `SGT
| `ULT -> `UGT
| `SGT -> `SLT
| `UGT -> `ULT
| `SGE -> `SLE
| `UGE -> `ULE
| `SLE -> `SGE
| `ULE -> `UGE

let pred_op_to_internal_rep = 
  function 
  | EQ -> `EQ
  | NEQ -> `NEQ
  | SLT -> `SLT
  | ULT -> `ULT
  | SGT -> `SGT
  | UGT -> `UGT
  | SGE -> `SGE
  | UGE -> `UGE


let get_comp_fun = function 
| `EQ -> CircularLinearProgression.intersection
| `NEQ -> raise (Failure "need to implement set difference")
| `SLT -> CircularLinearProgression.limit_lt_signed
| `ULT ->  CircularLinearProgression.limit_lt_unsigned
| `SGT -> CircularLinearProgression.limit_gt_signed
| `UGT -> CircularLinearProgression.limit_gt_unsigned
| `SGE -> CircularLinearProgression.limit_gte_signed
| `UGE -> CircularLinearProgression.limit_gte_unsigned
| `SLE -> CircularLinearProgression.limit_lte_signed
| `ULE -> CircularLinearProgression.limit_lte_unsigned


let denote_comp with_op to_limit with_val = let op_fun = ValueStore.ValueSet.pairwise_function_inclusive ~f:(get_comp_fun with_op) in op_fun to_limit with_val

let constrain_var (v: var) (curr_store: ValueStore.AbstractStore.t) with_op (with_val: ValueStore.ValueSet.t) =
  let v_val = ValueStore.AbstractStore.get curr_store (ValueStore.ALoc.Var v) in 
 ValueStore.ALoc.Map.set curr_store ~key:(ValueStore.ALoc.Var v) ~data:(denote_comp with_op v_val with_val)
  







let limit_var lv vs with_op (with_val: word) = 
constrain_var lv vs with_op (ValueStore.ValueSet.abstract_constant with_val)


let limit_two_vars comp lv rv vs =   let constrained_by_left = constrain_var lv vs comp (ValueStore.AbstractStore.get vs (ValueStore.ALoc.Var rv)) in
let constrained_by_right = constrain_var rv constrained_by_left (flip_comp comp) (ValueStore.AbstractStore.get vs (ValueStore.ALoc.Var rv))
in constrained_by_right

    let signed_op  op x y = op (Word.signed x) (Word.signed y)
    let unsigned_op op x y = op (Word.unsigned x) (Word.unsigned y)
    let concrete_op_from_pred_op (pred: predicate_op) =
      match pred with 
        | EQ -> Word.equal
        | NEQ -> (fun x y -> Word.equal x y |> not)
        | SLT -> signed_op Word.(<)
        | ULT -> unsigned_op Word.(<)
        | SGT -> signed_op Word.(>)
        | UGT -> unsigned_op Word.(>)
        | SGE -> signed_op Word.(>=)
        | UGE -> unsigned_op Word.(>=)

    let rec compute_known_form (kf: known_exp) (dom: VsaDom.t): BoolDom.t = 
      let (imms,vs) = dom in 
        match kf with 
          | Atom a -> calculate_atom a dom
          | Connective (op, exp1, exp2) -> compute_connective op exp1 exp2 dom
          | Predicate (op, exp1, exp2) -> compute_predicate op exp1 exp2 dom
      and compute_connective (op: connective_op) (exp1: known_exp) (exp2: known_exp) (pred: VsaDom.t): BoolDom.t = 
        let (exp1_t_approx, exp1_f_approx) = compute_known_form exp1 pred in 
        let (exp2_t_approx, exp2_f_approx) = compute_known_form exp2 pred in 
        let exp2_b = compute_known_form exp2 in
        match op with 
        | AND -> (ValueStore.AbstractStore.meet exp1_t_approx exp2_t_approx, ValueStore.AbstractStore.join exp2_f_approx exp1_f_approx)
        | OR -> (ValueStore.AbstractStore.join exp1_t_approx exp2_t_approx, ValueStore.AbstractStore.meet exp1_f_approx exp2_f_approx)
      and compute_predicate (op: predicate_op) (atom1: atom) (atom2: atom) (dom: VsaDom.t): BoolDom.t =
        let (imms, abstore) = dom in 
        let generalized_op = pred_op_to_internal_rep op in
        match (atom1, atom2) with 
          | (Var v1,  Var v2) -> (limit_two_vars generalized_op v1 v2 abstore, limit_two_vars(neg_of_comp generalized_op) v1 v2 abstore)
          | (Var v1, Int const2) -> (limit_var v1 abstore generalized_op const2 , limit_var v1 abstore (neg_of_comp generalized_op) const2)
          | (Int const1, Var v2) -> let flipped_op = flip_comp generalized_op in 
          (limit_var v2 abstore flipped_op const1 , limit_var v2 abstore (neg_of_comp flipped_op) const1)
          | (Int a, Int b) -> 
              let res = (concrete_op_from_pred_op op) a b in
                if res then (abstore,abstore) else (ValueStore.AbstractStore.bot, ValueStore.AbstractStore.bot)

end

           

(*
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
*)
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

    let dom: T.t option Knowledge.domain = KB.Domain.define ~join:(fun x y -> match (x,y) with
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
end)(struct let name = "compute_vsa_domain" end)



module ProduceBoolDom = FlatDomain(struct 
type t = VsaDom.t -> BoolDom.t
end)(struct let name = "compute_bool_dom" end)


module ProduceValueSet = FlatDomain(struct 
  type t = ValueStore.AbstractStore.t -> ValueStore.ValueSet.t
end)(struct let name = "compute_valueset" end)

module ProduceAbstractStore = struct 
include FlatDomain(struct type t = ValueStore.AbstractStore.t ->  ValueStore.AbstractStore.t end)(struct let name = "produce_value_store" end)

end

module ProduceBoolean = FlatDomain(struct 
  type t = VsaDom.t -> BoolDom.t
end)(struct let name = "compute_valueset" end)

let preds_set = KB.Domain.powerset (module Tid) "prececessors"


let post_conds = KB.Domain.mapping

let valueset_map ~f:(f:ValueStore.ValueSet.t -> ValueStore.ValueSet.t) (x: ProduceValueSet.t) = Option.map ~f:(fun producer -> fun ctxt -> f (producer ctxt)) x

let compute_exp_slot : (Theory.Value.cls, (ValueStore.AbstractStore.t -> ValueStore.ValueSet.t) option) Knowledge.slot= KB.Class.property ~package:"bap_ai" Theory.Value.cls  ~public:true "exp_value" ProduceValueSet.dom

let compute_mem_slot : (Theory.Value.cls, (ValueStore.AbstractStore.t -> ValueStore.AbstractStore.t) option) Knowledge.slot = KB.Class.property ~package:"bap_ai" Theory.Value.cls  ~public:true "exp_mem_slot" ProduceAbstractStore.dom

let tid_slot = KB.Class.property  ~package:"bap_ai" Theory.Effect.cls ~public:true "tid" (KB.Domain.obj Theory.Program.cls)

let precondition = KB.Class.property ~package:"bap_ai" Theory.Program.cls ~public:true "precondition" VsaKBDom.dom

(*to keep convenient we just keep postconditions for effects*)
let postcondition = KB.Class.property ~package:"bap_ai" Theory.Effect.cls ~public:true "postcondition" VsaKBDom.dom

let known_form_slot = KB.Class.property ~package:"bap_ai" Theory.Value.cls ~public:false "is_known_form" (KB.Domain.flat ~equal:KnownForm.equal ~empty:None "known_form_exp")


(*let predecessor_slot = KB.Class.property ~package:"bap_ai" Theory.Program.cls ~public:true "predecessors" (KB.Domain.powerset (module Theory.Label) "label_set")*)

(*ok so the idea here is we collect stuff based on our generated tid*)

let fresh = KB.Object.create Theory.Program.cls



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

module SolvableBooleanExpressions = struct 
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

  

  let unop s f x = lift mk_bv s f x

  let chain_with ~f:(f:ValueStore.ValueSet.t-> ValueStore.ValueSet.t) (f_orig: ProduceValueSet.t)  = Monads.Std.Monad.Option.Syntax.(
     !$(fun prev -> fun vstore -> f (prev vstore)) f_orig
  )

  let apply_function f x = chain_with ~f:(ValueStore.ValueSet.apply_function ~f:f) x
  
    
  let unop_app s x ~f:(f:ClpDomain.t -> ClpDomain.t) = unop s (apply_function f) x

  let unop_same x ~f:(f:ClpDomain.t -> ClpDomain.t) = unop_app same_sort x ~f:f

  let unop_bool x ~f:(f:ClpDomain.t -> ClpDomain.t) = unop_app bool_sort x ~f:f

  let not x = unop_same  ~f:CircularLinearProgression.not_clp x

  let neg x = unop_same  ~f:CircularLinearProgression.neg x
 

  let binop s f x y = lift2 mk_bv s f x y


  let chain2 ~f:(f: ValueStore.ValueSet.t -> ValueStore.ValueSet.t -> ValueStore.ValueSet.t) (forig1: ProduceValueSet.t) (forig2: ProduceValueSet.t) = Monads.Std.Monad.Option.Syntax.(
    !$$ (fun forig1 forig2 -> fun vstore -> f (forig1 vstore) (forig2 vstore)) forig1 forig2)

  let binop_pairwise_inclusive x y ~f:(f:ClpDomain.t -> ClpDomain.t -> ClpDomain.t) = chain2 ~f:(ValueStore.ValueSet.pairwise_function_inclusive ~f:f) x y
 

  let binop_app s x y ~f:(f:ClpDomain.t -> ClpDomain.t -> ClpDomain.t) = binop s (binop_pairwise_inclusive ~f:f) x y

  let binop_same x y ~f:(f:ClpDomain.t -> ClpDomain.t -> ClpDomain.t) = binop_app same_sort2 ~f:f x y

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
              ) v_func body_func))))


  let ite (b: Theory.bool) (th: 'a Theory.pure) (el: 'a Theory.pure) = b >>= (fun b ->
    th >>= (fun th -> 
      el >>= (fun el ->
        let b = (value b) in
        let new_th = (value th) in 

        let el = (value el) in 
        mk_bv (Theory.Value.sort th)
        Monads.Std.Monad.Option.Syntax.(

          !$$$ (fun b th el -> fun vstore -> 
            let bres = b vstore |> ValueStore.ValueSet.get_constants in 
            if (CircularLinearProgression.is_true bres) then
              th vstore

            else if (CircularLinearProgression.is_false bres) then
              el vstore
            else
              ValueStore.ValueSet.join (th vstore) (el vstore)
            ) b new_th el

        )
        
        )
      
      )
    )
  
  let denote_constant (w: word) = (Some (fun _ -> ValueStore.ValueSet.abstract_constant w))
  let b0 = mk_bv Theory.Bool.t (denote_constant Word.b0)

  let b1 = mk_bv Theory.Bool.t (denote_constant Word.b1)

  (* this probably isnt right but im lazy *)
  let inv (b: Theory.bool) =  unop_same  ~f:CircularLinearProgression.not_clp b


  let and_ (x: Theory.bool) (y: Theory.bool) = binop_same ~f:(CircularLinearProgression.logand) x y

  let or_ x y = binop_same ~f:(CircularLinearProgression.logor) x y

  let int (s: 's Theory.Bitv.t Theory.Value.sort) (w: Theory.word) = mk_bv s (denote_constant (Word.create w (Theory.Bitv.size s)))

  
  let msb (v: 's Theory.bitv) = unop_bool ~f:(CircularLinearProgression.msb) v

  let lsb (v: 's Theory.bitv) = unop_bool ~f:(CircularLinearProgression.lsb) v
  
  let add (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.add x y 

  let sub (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.sub x y


  let mul (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.unsigned_mul x y
  
  let div (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.unsigned_div x y
  

  let sdiv (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.signed_div x y
  
  let modulo (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.unsigned_modulo x y

  let smodulo (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.signed_modulo x y

  let logand  (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.logand x y
  
  let logor  (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.logor x y
  
  let logxor  (x: 's Theory.bitv) (y: 's Theory.bitv) = binop_same ~f:CircularLinearProgression.logxor x y
  
  (*
  let shiftr  (s: Theory.bool) (x: 's Theory.bitv) (y: 'b Theory.bitv) = binop_same ~f:CircularLinearProgression.shiftr x y*)
  

  
let exec_cast_on (ctype: cast) (v: ValueStore.ValueSet.t) (target_width: int) = let f = match ctype with 
| UNSIGNED -> CircularLinearProgression.zero_extend ~width:target_width
| SIGNED -> CircularLinearProgression.sign_extend ~width:target_width
| HIGH ->  CircularLinearProgression.shrink_high ~width:target_width (*narrow keeping high bit*)
| LOW ->  CircularLinearProgression.shrink_low ~width:target_width (*narrow keeping low bits*)
in
ValueStore.ValueSet.apply_function ~f:f v



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


(**

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
*)


  let variable_is_bool (v: _ Theory.var) = 
    let s = Theory.Var.sort v in 
    let b = Theory.Bitv.define 1 in 
      Theory.Value.Sort.same b s


  let get_bool (v: ValueStore.ValueSet.t) =
     let const_val = ValueStore.ValueSet.get_constants v in
     if CircularLinearProgression.is_true const_val then
      `True
     else if CircularLinearProgression.is_false const_val then
      `False
     else
      `Top


      (*
    Ok first we need to check the inferred value, if it is not top then we can set values accordingly
      ie. if is always true then (abstore, bot)
        if always false (bot, abstore)

        otherwise if it a known form we can apply a computation of the known form

          finally we have to give up and say the value of the boolean is (abstore,abstore)
    
    *)

  let pure_exp_as_bool (p: _ Theory.Value.t) (pred: VsaDom.t) = 
    let (immenv, abstore) = pred in 
    let b_val = (Option.value_exn (value p)) abstore |> get_bool in (* TODO do something about this*) 
    match b_val with 
      | `True -> (abstore, ValueStore.AbstractStore.bot)
      | `False -> (ValueStore.AbstractStore.bot, abstore)
      | `Top -> 
        let kf: KnownForm.T.t = SolvableBooleanExpressions.value p in 
        Option.map ~f:(fun some_kf -> KnownForm.compute_known_form some_kf pred) kf |> Option.value ~default:(abstore,abstore)
  

  let variable_is_mem (v: _ Theory.var) = 
    let s = Theory.Var.sort v in 
    let s = Theory.Value.Sort.forget s in
    Theory.Mem.refine s |> Option.is_some

    
  let compute_store (v: _ Theory.var) (p: _  Theory.Value.t) (abstore: ValueStore.AbstractStore.t): ValueStore.AbstractStore.t  = 
    let mem_repr: _ -> ValueStore.AbstractStore.t = KB.Value.get compute_mem_slot p |> Option.value_exn in
      let next_abstore = mem_repr abstore in
        next_abstore



  let compute_exp (v: _ Theory.var) (p: _ Theory.Value.t) (abstore: ValueStore.AbstractStore.t): ValueStore.AbstractStore.t  = 
    let val_repr: _ -> ValueStore.ValueSet.t = KB.Value.get compute_exp_slot p |> Option.value_exn in
    let nval = val_repr abstore in 
      ValueStore.ALoc.Map.set abstore ~key:(aloc_from_theory v) ~data:nval

  let set (v: _ Theory.var) (p: _ Theory.pure) = 
    let tid_update = 
      let* tid = fresh in
      let* pred = KB.collect precondition tid  in 
      let (bool_env, curr_abstract_store) = pred in
      let v_aloc = aloc_from_theory v in 
      let reify_v = Var.reify v in 
      let is_bool = variable_is_bool v in 
      let* pval = p in 
      let post_cond = if is_bool then 
        (Var.Map.set bool_env ~key:reify_v ~data:(pure_exp_as_bool pval pred), curr_abstract_store)
      else 
        (* there are two types of assignments we have to handle assignments into memory and assignments into a normal var*)
      let denote_def' (astore: ValueStore.AbstractStore.t): ValueStore.AbstractStore.t = if variable_is_mem v then 
          (* TODO this doesnt work with multiple memories *)
          compute_store v pval astore
      else
        compute_exp v pval astore  in

        (Var.Map.map bool_env ~f:(fun (t,f) -> denote_def' t,  denote_def' f) , denote_def' curr_abstract_store)
      in
      let empty_denotation =  (Theory.Effect.empty (Theory.Effect.Sort.data "")) in 
      let post_cond_denot = KB.Value.put postcondition empty_denotation post_cond in 
      let add_tid_denot = KB.Value.put tid_slot post_cond_denot tid in
      KB.return post_cond_denot
  in
    tid_update


end 

let () =
  Theory.declare ~name:"vsa_denotation" 
  (
   Theory.instance ()
    >>= Theory.require >>| fun (module BaseM): Theory.core ->
      (module struct 
        include BaseM 
        include Denotation
    end)
  )