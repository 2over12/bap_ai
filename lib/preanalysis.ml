open Bap.Std
open Core_kernel

(*
Goal: Generate the aloc map structure
*)



let directly_calls ~target (c: Call.t) = match Call.target c with 
  | Indirect _ -> false
  | Direct t -> Tid.equal target t

let is_indirect_call (c: Call.t) = match Call.target c with 
  | Indirect _ -> true
  | _ -> false 


let extract_call (j: Jmp.t) = 
  match Jmp.kind j with 
    | Call c -> Some c
    | _ -> None



let get_calls_from_sub (proc: Sub.t) = 
  let jumps =  Seq.concat_map ~f:(fun blk -> Term.enum jmp_t blk) (Term.enum blk_t proc)  in
  let calls = Seq.filter_map ~f:(extract_call) jumps in calls
(*
This function must conservatively claim that a function is not recursive 

In the future perhaps we can use the results of VSA to make better approximations of indirect calls
*)
let is_function_not_recursive (proc: Sub.t) =
  let calls = get_calls_from_sub proc in
  not ( Seq.exists ~f:is_indirect_call calls || Seq.exists ~f:(directly_calls ~target:(Term.tid proc)) calls) 

let collect_non_recursive_functions (prog: Program.t) = 
  Seq.filter_map ~f:(fun s -> if is_function_not_recursive s then Some (Term.tid s) else None) (Term.enum sub_t prog)


let get_stack_variables (proc: Sub.t) = 
  let calls = 