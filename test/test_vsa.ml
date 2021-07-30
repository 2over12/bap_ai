open Bap.Std
open Core_kernel


let x_var = Var.create "x" (Bil.Types.Imm 32)
let y_var = Var.create "y" (Bil.Types.Imm 32)

let setxto1 = Def.create x_var (Bil.Int  (Word.of_int 1 ~width:32))

let setxto4 = Def.create x_var (Bil.Int  (Word.of_int 4 ~width:32))

let set_y_to_2 = Def.create x_var (Bil.Int  (Word.of_int 4 ~width:32))

let set_x_to_xy = Def.create x_var (Bil.BinOp (Bil.PLUS, (Bil.Var x_var), (Bil.Var y_var))) 

let create_1_def_block ?jmp_targets:(jmp_targets = []) df  = 
  let blk_builder = Blk.Builder.create () in 
  Blk.Builder.add_def blk_builder df;
  List.iter ~f:(fun tgt -> Blk.Builder.add_jmp blk_builder tgt ) jmp_targets;
  Blk.Builder.result blk_builder


  let sum_block = 
    create_1_def_block set_x_to_xy 




  let set_x_1_block = create_1_def_block  setxto1 ~jmp_targets:[Jmp.create_goto (Direct (Term.tid sum_block))]



  let set_x_4_block = 
    create_1_def_block setxto4 ~jmp_targets:[Jmp.create_goto (Direct (Term.tid sum_block))]

  let set_y_block = 
    create_1_def_block set_y_to_2 ~jmp_targets:([Jmp.create_goto ~cond:(Bil.BinOp  ((Bil.LT, (Bil.Var y_var), (Bil.Int (Word.one 32))))) (Direct (Term.tid set_x_1_block));
    Jmp.create_goto (Direct (Term.tid set_x_4_block))])



  




(*let t = 
  let empty_grph = Graphs.Ir.empty in 
*)
