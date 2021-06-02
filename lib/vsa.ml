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


let denote_comp (comp: binop) (lh: ValueStore.ValueSet.t) (rh:  ValueStore.ValueSet.t) = 
let op_to_apply = 
match comp with 
| EQ -> CircularLinearProgression.intersection
| NEQ -> raise (Failure "need to implement set difference to apply this constraint")
| LT -> CircularLinearProgression.less_than_unsigned
| LE -> CircularLinearProgression.lte_unsigned
| SLT -> CircularLinearProgression.less_than_signed
| SLE -> CircularLinearProgression.lte_signed
| _ -> raise (Failure "impossible")
in 
  ValueStore.ValueSet.pairwise_function_inclusive ~f:(op_to_apply) lh rh



let handle_predicate (comp: binop) (lh: exp) (rh: exp) (vs: ValueStore.AbstractStore.t): BoolDom.t = match (lh,rh) with 
  | (Bil.Var lv, Bil.Var rv) -> (vs,vs)
  | (Bil.Var lv, Bil.Int ri) -> (vs, vs)
  | (Bil.Int li, Bil.Var rv) -> (vs, vs)
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
                                                                                                                                                                                                                                                                                                                                               

let denote_def  (d: Def.t) (pred: VsaDom.t): VsaDom.t = 
  let assignee  = Def.lhs d in
  let (imms, vs) = pred in 
  if is_bool assignee then  
    (Var.Map.update imms assignee
    ~f:(fun _ -> denote_exp_as_bool (Def.rhs d) pred), vs)
  else
  (*if we arent updating a boolean *)
  let denote_def' : ValueStore.AbstractStore.t -> ValueStore.AbstractStore.t = raise (Failure "havent implemented def denotations yet")
in (Var.Map.map imms ~f:(fun (t,f) -> denote_def' t,  denote_def' f) , denote_def' vs)
