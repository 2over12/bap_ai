open Bap_ai
open OUnit2
open Core_kernel

let ex_clp n = ({width=8;card=(Z.of_int n);step=(Z.of_int 48); base=(Z.of_int 216)}:(CircularLinearProgression.canon CircularLinearProgression.t))

let create_alp ~width ~card ~step base = ({width=width;card=card;step=step; base=base}:(CircularLinearProgression.alp CircularLinearProgression.t))

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

  let test_calculate_gap_ncanon _ = let res = CircularLinearProgression.compute_gap_width (ex_clp 15) in assert_equal ({ia=Z.of_int 11;ib=Z.of_int 5; alpha=Z.of_int 16;beta= Z.of_int 16}:CircularLinearProgression.computed_clp_facts) res

  let test_calculate_gap_ex_ncanon _ = let res = CircularLinearProgression.compute_gap_width_ex (ex_clp 15) Z.zero in assert_equal (({ia=Z.of_int 11;ib=Z.of_int 5;alpha=Z.of_int 16;beta=Z.of_int 16}:CircularLinearProgression.computed_clp_facts), ( Z.one,Z.of_int 8)) res

  
  let test_calculate_gap_ex_ncanonother _ = let res = CircularLinearProgression.compute_gap_width_ex (ex_clp 15) (Z.of_int 91) in assert_equal (({ia=Z.of_int 11;ib=Z.of_int 5;alpha=Z.of_int 16;beta=Z.of_int 16 }:CircularLinearProgression.computed_clp_facts),(Z.of_int 3,Z.of_int 13)) res


  
  let test_calculate_gap_ex_on_point _ = let res = CircularLinearProgression.compute_gap_width_ex (ex_clp 15) (Z.of_int 216) in assert_equal (({ia=Z.of_int 11;ib=Z.of_int 5; alpha=Z.of_int 16;beta=Z.of_int 16}:CircularLinearProgression.computed_clp_facts),((Z.of_int 0),Z.of_int 0)) res

  let test_incision_alp_split _ = let start_clp = CircularLinearProgression.create ~width:8 ~card:(Z.of_int 10) ~step:(Z.of_int 30) (Z.of_int 60) in
    let alps = CircularLinearProgression.unsigned_alps start_clp in assert_equal ~printer:(fun x -> List.map ~f:clp_printer x |> List.fold ~init:"" ~f:(fun accum x -> accum ^ "|"^x)) [
      create_alp ~width:8 ~card:(Z.of_int 7) ~step:(Z.of_int 30) (Z.of_int 60);
      create_alp ~width:8 ~card:(Z.of_int 3) ~step:(Z.of_int 30) (Z.of_int 14);
    ] alps  

    let test_incision_alp_split_signed _ = let start_clp = CircularLinearProgression.create ~width:8 ~card:(Z.of_int 10) ~step:(Z.of_int 30) (Z.of_int 60) in
    let alps = CircularLinearProgression.signed_alps start_clp in assert_equal ~printer:(fun x -> List.map ~f:clp_printer x |> List.fold ~init:"" ~f:(fun accum x -> accum ^ "|"^x)) [
      create_alp ~width:8 ~card:(Z.of_int 3) ~step:(Z.of_int 30) (Z.of_int 60);
      create_alp ~width:8 ~card:(Z.of_int 7) ~step:(Z.of_int 30) (Z.of_int (-106));
    ] alps  
  let suite =
  "Test CLPs" >::: [
    "test_canon_casea" >:: test_canon_casea;
    "test_canon_caseb" >:: test_canon_caseb;
    "test_canon_casec" >:: test_canon_casec;
    "test_calculate_gap_ncanon" >:: test_calculate_gap_ncanon;
    "test_calculate_gap_ex_ncanon" >:: test_calculate_gap_ex_ncanon; 
    "test_calculate_gap_ex_ncanonother" >::test_calculate_gap_ex_ncanonother;
    "test_calculate_gap_ex_ncanonother" >:: test_calculate_gap_ex_on_point;
    "test_incision_alp_split" >:: test_incision_alp_split;
    "test_incision_alp_split_signed" >:: test_incision_alp_split_signed
  ]

let () =
  run_test_tt_main suite
