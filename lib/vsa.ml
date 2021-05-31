open Core_kernel
open Bap.Std

module VsaDom = ProductDomain.BottomReduction(ImmEnv.BooleanImmediates)(ValueStore.AbstractStore)

let is_bool (v: Var.t) = Var.typ v |> function 
  | Type.Imm x -> Int.equal x 1 
  | _ -> false


  (* goal here is to return both an overapproximation of true and overapproximation of false... i think this should be calculable
  any non boolean thing should be pulled from normal denotation. Could sparse up the repr by only considering variables that will be needed later, some sort of backwards slicing on bools.*)
let denote_exp_as_bool (e: Exp.t) (pred: VsaDom.t): ProductDomain.MakeProduct(ValueStore.AbstractStore)(ValueStore.AbstractStore).t =
  let (imms,vs) = pred in 
  match e with 
    | Bil.Var x -> Option.value  ~default:(ValueStore.AbstractStore.bot, ValueStore.AbstractStore.bot) (Var.Map.find imms x)
    | Bil.Int x -> if Word.equal (Word.one 1) x then  (vs, ValueStore.AbstractStore.bot) else  (ValueStore.AbstractStore.bot, vs)
    | _ -> raise (Failure "exp not supported yet")

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
