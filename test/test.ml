open Bap_ai
open OUnit2
open Core_kernel

let ex_clp n = CircularLinearProgression.create ~width:8 ~step:(Z.of_int 48) ~card:(Z.of_int n) (Z.of_int 216)

let clp_printer v = CircularLinearProgression.sexp_of_t v |> Sexp.to_string

let test_canon_casea _ = 
  let c = ex_clp 19 in 
  let c_canon = CircularLinearProgression.canonize c in
  assert_equal ~printer:clp_printer (CircularLinearProgression.create  ~width:8 ~step:(Z.of_int 16) ~card:(Z.of_int 16) (Z.of_int 8)) c_canon 


let test_canon_caseb _ = 
  let c = ex_clp 15 in 
  let c_canon = CircularLinearProgression.canonize c in
  assert_equal ~printer:clp_printer (CircularLinearProgression.create  ~width:8 ~step:(Z.of_int 16) ~card:(Z.of_int 15) (Z.of_int 184)) c_canon 

let test_canon_casec _ = 
  let s = CircularLinearProgression.create ~width:8 ~step:(Z.of_int 132) ~card:(Z.of_int 7) (Z.of_int 90) in 
  assert_equal ~printer:clp_printer (CircularLinearProgression.create  ~width:8 ~step:(Z.of_int 124) ~card:(Z.of_int 7) (Z.of_int 114)) (CircularLinearProgression.canonize s)
let suite =
  "Test CLPs" >::: [
    "test_canon_casea" >:: test_canon_casea;
    "test_canon_caseb" >:: test_canon_caseb;
    "test_canon_casec" >:: test_canon_casec
  ]

let () =
  run_test_tt_main suite