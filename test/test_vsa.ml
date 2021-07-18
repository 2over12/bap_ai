
open Core_kernel
open Bap_core_theory
open Bap_ai
open Bap_knowledge
open Knowledge.Syntax
open OUnit2



type dword

type 'a reg = 'a Theory.Bitv.t Theory.var
type 'a sort = 'a Theory.Bitv.t Theory.Value.sort

let s32: dword sort = (Theory.Bitv.define 32)
let x: dword reg = Theory.Var.define s32 "X"

let y: dword reg = Theory.Var.define s32 "Y"

let z: dword reg = Theory.Var.define s32 "Z"

let theory =  Theory.instance ~requires:["vsa_denotation"] () >>= Theory.require

let attempt_to_create_var = theory >>= (fun vsa -> 
  let module X = (val vsa : Theory.Core) in 
  let x_v = X.var x in
  let y_v = X.var y in 
  let set_x = X.set x (X.int s32 Bitvec.zero ) in
  let set_y = X.set y (X.int s32 Bitvec.one) in

  let set_z = X.set z (X.add x_v y_v) in 
  X.seq set_x (X.seq set_y set_z))

let res_obj = KB.Object.create Theory.Effect.cls

let get_res target = 
  let empty_state = KB.empty in
    let n_obj = target >>= (fun ntarget-> 
      let tv = KB.Value.get Vsa.compute_post_condidtion ntarget in
      res_obj >>= (fun res_obj -> KB.provide Vsa.compute_post_condidtion res_obj tv >>= (fun _ -> KB.return res_obj))) in
    KB.run Theory.Effect.cls n_obj empty_state

let get_unconflicted_res target = Option.value_exn (get_res target |> Result.ok)
let test_add10 _ = 
  let v, _ = get_unconflicted_res attempt_to_create_var in 
  let post_cond = KB.Value.get Vsa.compute_post_condidtion v in
  assert_bool "post_cond is not bottom" (Option.is_none post_cond)



let test_vsa =  "Test CLPs" >::: [ "test_add10" >:: test_add10  ]
let _ = run_test_tt_main test_vsa
