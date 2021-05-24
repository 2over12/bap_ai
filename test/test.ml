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


    let test_slow_alp_split_signed _ = let start_clp =  CircularLinearProgression.create ~width:8 ~card:(Z.of_int 20) ~step:(Z.of_int 124) (Z.of_int 10) in
    let alps = CircularLinearProgression.signed_alps start_clp in assert_equal ~printer:(fun x -> List.map ~f:clp_printer x |> List.fold ~init:"" ~f:(fun accum x -> accum ^ "|"^x)) [
      create_alp ~width:8 ~card:(Z.of_int 2) ~step:(Z.of_int 60) (Z.of_int (-122));
      create_alp ~width:8 ~card:(Z.of_int 9) ~step:(Z.of_int 8) (Z.of_int (-54));
      create_alp ~width:8 ~card:(Z.of_int 9) ~step:(Z.of_int 8) (Z.of_int 62);
    ] alps  



    let test_slow_alp_split_unsigned _ = let start_clp =  CircularLinearProgression.create ~width:8 ~card:(Z.of_int 20) ~step:(Z.of_int 124) (Z.of_int 10) in
    let alps = CircularLinearProgression.unsigned_alps start_clp in assert_equal ~printer:(fun x -> List.map ~f:clp_printer x |> List.fold ~init:"" ~f:(fun accum x -> accum ^ "|"^x)) [
      create_alp ~width:8 ~card:(Z.of_int 2) ~step:(Z.of_int 8) (Z.of_int 2);
      create_alp ~width:8 ~card:(Z.of_int 10) ~step:(Z.of_int 8) (Z.of_int 62);
      create_alp ~width:8 ~card:(Z.of_int 8) ~step:(Z.of_int 8) (Z.of_int 194);
    ] alps  

  (*TODO should probably generate zarith ints to allow for bigints*)
  let clp_gen = QCheck.Gen.((int_range 2 12)
  >>= (fun width -> 
    map 
      (fun vals -> CircularLinearProgression.Z.Set.of_list vals |> CircularLinearProgression.abstract ~width:width) 
      (map (fun a -> List.map ~f:CircularLinearProgression.Z.of_int a) (list int))
      ))

  let print_clp c = CircularLinearProgression.sexp_of_t c |> Sexp.to_string
 
  (*maybe can do better?*)
  let shrink_clp (c: CircularLinearProgression.canon CircularLinearProgression.t) =  QCheck.Iter.map (fun new_card -> CircularLinearProgression.create ~width:c.width ~card:(Z.of_int new_card) ~step:c.step c.base) (QCheck.Shrink.int (c.card|> Z.to_int))
  
  let arbitrary_clp = QCheck.make ~print:print_clp ~shrink:shrink_clp clp_gen

  
  let test_unary_operator abstract_op concrete_op concretization_function ~count = QCheck.Test.make ~count:count arbitrary_clp (fun a -> 
    let concrete_values = concretization_function a in
    let resulting_concrete_values = CircularLinearProgression.Z.Set.map ~f:concrete_op concrete_values in 
    let resulting_abstract_values = abstract_op a |> concretization_function  in
    CircularLinearProgression.Z.Set.is_subset resulting_abstract_values ~of_:resulting_concrete_values
  )

  let test_neg = QCheck_ounit.to_ounit2_test  (test_unary_operator CircularLinearProgression.neg CircularLinearProgression.Z.neg CircularLinearProgression.signed_concretize ~count:200)

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
    "test_incision_alp_split_signed" >:: test_incision_alp_split_signed;
    "test_slow_alp_split_signed" >:: test_slow_alp_split_signed;
    "test_slow_alp_split_unsigned" >:: test_slow_alp_split_unsigned;test_neg
  ]

let () =
  run_test_tt_main suite
