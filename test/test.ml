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


let test_canon_0step _ = let c = ({width=3;step=(Z.of_int 224);card=(Z.of_int 2);base=(Z.of_int 2)}:(CircularLinearProgression.canon CircularLinearProgression.t)) in
  let c_canon = CircularLinearProgression.canonize c in 
   assert_equal  ~printer:clp_printer (CircularLinearProgression.create  ~width:3 ~step:(Z.of_int 0) ~card:(Z.of_int 1) (Z.of_int 2)) c_canon

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
(*
  let clp_gen = QCheck.Gen.((int_range 2 12)
  >>= (fun width -> 
    map 
      (fun vals -> CircularLinearProgression.Z.Set.of_list vals |> CircularLinearProgression.abstract ~width:width) 
      (map (fun a -> List.map ~f:CircularLinearProgression.Z.of_int a) (list int))
      ))*)


  let clp_gen = QCheck.Gen.(let width_gen = (int_range 1 12) in
  let member_gen = map Z.of_int (graft_corners int int_corners ()) in
  let card_gen = map Z.of_int (graft_corners nat int_pos_corners ()) in
  quad width_gen member_gen member_gen card_gen
  >|=fun (width, base,step,card) -> 
      CircularLinearProgression.create ~width:width ~step:step ~card:card base
      )

  let print_clp c = CircularLinearProgression.sexp_of_t c |> Sexp.to_string
 
  (*maybe can do better?*)
  let shrink_clp (c: CircularLinearProgression.canon CircularLinearProgression.t) =  QCheck.Iter.map (fun new_card -> CircularLinearProgression.create ~width:c.width ~card:(Z.of_int new_card) ~step:c.step c.base) (QCheck.Shrink.int (c.card|> Z.to_int))
  
  let arbitrary_clp = QCheck.make ~print:print_clp ~shrink:shrink_clp clp_gen


  let gen_clp_pair = QCheck.Gen.(pair clp_gen clp_gen |> map (fun ((a: CircularLinearProgression.canon CircularLinearProgression.t),(b: CircularLinearProgression.canon CircularLinearProgression.t)) 
    -> (a,CircularLinearProgression.create ~width:a.width ~step:b.step ~card:b.card b.base)))

  let print_clp_pair = QCheck.Print.pair print_clp print_clp

  let shrink_clp_pair = QCheck.Shrink.pair shrink_clp shrink_clp

  let arbitrary_clp_pair = QCheck.make ~print:print_clp_pair ~shrink:shrink_clp_pair gen_clp_pair
  
  let test_unary_operator ~name abstract_op concrete_op concretization_function reduction_function  compute_width ~count = QCheck.Test.make ~name:name ~count:count arbitrary_clp (fun a -> 
    (*print_endline (CircularLinearProgression.sexp_of_t a |> Sexp.to_string);*)
    let concrete_values = concretization_function a in
    let resulting_concrete_values = CircularLinearProgression.Z.Set.map ~f:(Fn.compose (reduction_function ~width:(compute_width a)) concrete_op) concrete_values in 
    let resulting_abstract_values = abstract_op a |> concretization_function  in
    CircularLinearProgression.Z.Set.is_subset resulting_concrete_values ~of_:resulting_abstract_values
  )

  let merge_by_applying_op v1 v2 (c1: CircularLinearProgression.canon CircularLinearProgression.t) (c2: CircularLinearProgression.canon CircularLinearProgression.t) (f: Z.t -> Z.t -> Z.t) reduction_function compute_width = 
    List.cartesian_product (CircularLinearProgression.Z.Set.to_list v1) (CircularLinearProgression.Z.Set.to_list v2) |> List.map ~f:(Fn.compose (reduction_function ~width:(compute_width c1 c2))  (fun (a,b) -> f a b)) 
    |> CircularLinearProgression.Z.Set.of_list


  let apply_binary_operator (c1: CircularLinearProgression.canon CircularLinearProgression.t) (c2: CircularLinearProgression.canon CircularLinearProgression.t)  ~concretization_function ~merge_values  = 
    let v1 = concretization_function c1 in 
    let v2 = concretization_function c2 in 
    merge_values  v1 v2 c1 c2
 
  

  let test_binary_operator_is_over_approx ~name abstract_op concretization_function compute_concrete_values ~count = QCheck.Test.make ~name:name ~count:count arbitrary_clp_pair (fun (c1,c2) -> 
    let concrete_values = compute_concrete_values c1 c2 in
    let resulting_abstract_values = abstract_op c1 c2 |> concretization_function in 
    CircularLinearProgression.Z.Set.is_subset concrete_values  ~of_:resulting_abstract_values
    )


  let test_unary_operator_same_width  abstract_op concrete_op concretization_function reduction_function ~count = test_unary_operator abstract_op concrete_op concretization_function reduction_function (fun a -> a.width) ~count

  let test_neg = QCheck_ounit.to_ounit2_test  (test_unary_operator_same_width ~name:"qcheckneg" CircularLinearProgression.neg CircularLinearProgression.Z.neg CircularLinearProgression.unsigned_concretize CircularLinearProgression.interpret_unsigned_value ~count:200)


  let test_not = QCheck_ounit.to_ounit2_test  (test_unary_operator_same_width  ~name:"qchecknot"CircularLinearProgression.not_clp CircularLinearProgression.Z.lognot CircularLinearProgression.signed_concretize CircularLinearProgression.interpret_signed_value ~count:200)

  let test_not_signed  = QCheck_ounit.to_ounit2_test (test_unary_operator_same_width  ~name:"qchecksignednot"CircularLinearProgression.not_clp CircularLinearProgression.Z.lognot CircularLinearProgression.signed_concretize CircularLinearProgression.interpret_signed_value ~count:200)

  let test_not_unsigned = QCheck_ounit.to_ounit2_test (test_unary_operator_same_width  ~name:"qcheckunsignednot" CircularLinearProgression.not_clp CircularLinearProgression.Z.lognot CircularLinearProgression.unsigned_concretize CircularLinearProgression.interpret_unsigned_value ~count:200)
  
  let test_union =QCheck_ounit.to_ounit2_test (test_binary_operator_is_over_approx ~name:"test_union" CircularLinearProgression.union CircularLinearProgression.unsigned_concretize 
    (apply_binary_operator ~concretization_function:CircularLinearProgression.unsigned_concretize ~merge_values:(fun v1 v2 _c1 _c2 -> CircularLinearProgression.Z.Set.union v1 v2)) ~count:200)
  

    let compute_concrete_interseciton=(apply_binary_operator ~concretization_function:CircularLinearProgression.unsigned_concretize ~merge_values:(fun v1 v2 _c1 _c2 -> CircularLinearProgression.Z.Set.inter v1 v2))

    let test_intersection =QCheck_ounit.to_ounit2_test (test_binary_operator_is_over_approx  ~name:"test_intersection" CircularLinearProgression.intersection CircularLinearProgression.unsigned_concretize 
    compute_concrete_interseciton ~count:200)
  


    
    let compute_pw_func ~f = (apply_binary_operator ~concretization_function:CircularLinearProgression.unsigned_concretize ~merge_values:(fun v1 v2 c1 c2 -> 
     List.map ~f:(fun (x,y) -> f c1 c2 x y) (List.cartesian_product (CircularLinearProgression.Z.Set.to_list v1) (CircularLinearProgression.Z.Set.to_list v2)) |> CircularLinearProgression.Z.Set.of_list)   )
      
    let compute_left_shifts = compute_pw_func ~f:(fun c1 _c2 x y -> Z.erem (Z.shift_left x (Z.to_int y )) (CircularLinearProgression.comp_size c1) )
  
     let test_left_shift = QCheck_ounit.to_ounit2_test (test_binary_operator_is_over_approx ~name:"test_left_shift"  CircularLinearProgression.left_shift CircularLinearProgression.unsigned_concretize 
     compute_left_shifts ~count:200)
  
     let compute_ors = compute_pw_func ~f:(fun _c1 _c2 x y -> Z.logor x y)

     let compute_ands = compute_pw_func ~f:(fun _c1 _c2 x y -> Z.logand x y)

     let compute_sub = compute_pw_func ~f:(fun c1 _c2 x y -> Z.erem (Z.sub x y) (CircularLinearProgression.comp_size c1))
     let test_or = QCheck_ounit.to_ounit2_test (test_binary_operator_is_over_approx ~name:"test_or"  CircularLinearProgression.logor CircularLinearProgression.unsigned_concretize 
     compute_ors ~count:200)

     let test_and = QCheck_ounit.to_ounit2_test (test_binary_operator_is_over_approx  ~name:"test_and" CircularLinearProgression.logand CircularLinearProgression.unsigned_concretize 
     compute_ands ~count:200)

     let compute_adds = compute_pw_func ~f:(fun c1 _c2 x y ->  Z.erem (Z.add x y) (CircularLinearProgression.comp_size c1) )

     let test_add = QCheck_ounit.to_ounit2_test (test_binary_operator_is_over_approx  ~name:"test_add" CircularLinearProgression.add CircularLinearProgression.unsigned_concretize 
     compute_adds ~count:200)


     let test_sub = QCheck_ounit.to_ounit2_test (test_binary_operator_is_over_approx  ~name:"test_sub" CircularLinearProgression.sub CircularLinearProgression.unsigned_concretize 
     compute_sub ~count:200)


  
  let collect_pairwise ~f x y = List.cartesian_product (CircularLinearProgression.Z.Set.to_list x) (CircularLinearProgression.Z.Set.to_list y) |> List.map ~f:(fun (x,y) -> f x y) |> CircularLinearProgression.Z.Set.of_list

  let shiftr_fill0_func: CircularLinearProgression.canon CircularLinearProgression.t -> CircularLinearProgression.canon CircularLinearProgression.t -> CircularLinearProgression.canon CircularLinearProgression.t = ((CircularLinearProgression.shift_right_fill (CircularLinearProgression.abstract_single_value Z.zero ~width:1)))

  let shiftr_fill1_func: CircularLinearProgression.canon CircularLinearProgression.t -> CircularLinearProgression.canon CircularLinearProgression.t -> CircularLinearProgression.canon CircularLinearProgression.t = ((CircularLinearProgression.shift_right_fill (CircularLinearProgression.abstract_single_value Z.one ~width:1)))
  let z_illogical_shift ~width:(width:int) (to_shift: Z.t) (by: int) = 
    let it = (Z.shift_right_trunc to_shift by) in
    let by_1s = (Z.pred (Z.shift_left Z.one by) ) in
    let diff = width-by in
    let or_mask = if diff < 0  then 
      (print_endline "shifting right";Z.shift_right_trunc by_1s (Int.abs diff))
  else 
      
      Z.shift_left by_1s diff in
    print_endline ("or_mask: " ^ Z.to_string or_mask ^ " orig by 1s: " ^ Z.to_string by_1s);
    Z.logor or_mask it

  let  test_shiftr_fill0 = QCheck_ounit.to_ounit2_test (test_binary_operator_is_over_approx ~name:"test_shiftr_fill0" shiftr_fill0_func CircularLinearProgression.unsigned_concretize 
  (apply_binary_operator ~concretization_function:CircularLinearProgression.unsigned_concretize ~merge_values:(fun v1 v2 _c1 _c2 -> 
    collect_pairwise ~f:(fun x y -> Z.shift_right_trunc x (Z.to_int y)) v1 v2)) ~count:200)


    let compute_right_shifts_fill1 = (apply_binary_operator ~concretization_function:CircularLinearProgression.unsigned_concretize ~merge_values:(fun v1 v2 c1 _c2 -> 
      collect_pairwise ~f:(fun x y -> z_illogical_shift ~width:c1.width  x (Z.to_int y)) v1 v2))
    let  test_shiftr_fill1 = QCheck_ounit.to_ounit2_test (test_binary_operator_is_over_approx  ~name:"test_shiftr_fill1" shiftr_fill1_func CircularLinearProgression.unsigned_concretize 
    compute_right_shifts_fill1 ~count:200)
  

  let shiftr_fill0_regression _ =
    let to_shift =  CircularLinearProgression.create ~width:3 ~step:Z.zero ~card:(Z.of_int 1) Z.one in
    let by = CircularLinearProgression.create ~width:3 ~step:Z.one ~card:(Z.of_int 8) Z.zero in
    let res = CircularLinearProgression.right_shift_unsigned to_shift by in 
    assert_equal ~printer:(clp_printer) (CircularLinearProgression.create ~width:3 ~step:Z.one ~card:(Z.succ Z.one) Z.zero) res 

  let neg_regression _  = let initial_clp = CircularLinearProgression.create ~width:9 ~step:Z.one ~card:(Z.of_int 257) Z.zero in
  let res_clp = CircularLinearProgression.neg initial_clp in 
   let resulting_values = res_clp |> CircularLinearProgression.signed_concretize |> CircularLinearProgression.Z.Set.to_list |> List.sort ~compare:CircularLinearProgression.Z.compare in 
   let expected_values = CircularLinearProgression.Z.Set.map ~f:(Fn.compose (CircularLinearProgression.interpret_signed_value ~width:initial_clp.width)  Z.neg) (CircularLinearProgression.signed_concretize initial_clp) |> CircularLinearProgression.Z.Set.to_list |> List.sort ~compare:CircularLinearProgression.Z.compare in 
    assert_equal ~printer:(fun s -> Sexp.List (List.map ~f:(fun a -> Sexp.Atom (Z.to_string a)) s )|>  Sexp.to_string) expected_values resulting_values

  let print_set s = CircularLinearProgression.Z.Set.sexp_of_t s |> Sexp.to_string


  
  let bin_op_regression (a: CircularLinearProgression.canon CircularLinearProgression.t) (b: CircularLinearProgression.canon CircularLinearProgression.t) abs_op concretization_function concrete_combine _ = 
    print_endline (print_clp a);
    print_endline (print_clp b);
    let abs_values = abs_op a b |> concretization_function in 
    let concrete_values = concrete_combine (concretization_function a) (concretization_function b) in 
    assert_bool ((print_set concrete_values) ^ "\n" ^(print_set abs_values)) (CircularLinearProgression.Z.Set.is_subset concrete_values  ~of_:abs_values)

  
  let create_union_regression a b =  bin_op_regression a b CircularLinearProgression.union CircularLinearProgression.unsigned_concretize CircularLinearProgression.Z.Set.union

  
  let union_regression: test_ctxt -> unit = let a =  CircularLinearProgression.create ~width:6 ~step:(Z.of_int 16) ~card:(Z.of_int 2) (Z.of_int 10) in
      let b = CircularLinearProgression.create ~width:6 ~step:Z.zero  ~card:Z.one Z.zero in
      create_union_regression a b
    
  let union_regression2: test_ctxt -> unit = create_union_regression (CircularLinearProgression.create ~width:11 ~card:(Z.of_int 3) ~step:(Z.of_int 866) (Z.of_int 855)) (CircularLinearProgression.create ~width:11 ~card:(Z.of_int 1) ~step:(Z.of_int 0) (Z.of_int 41))


  let union_regression3 = create_union_regression (CircularLinearProgression.create ~width:3 ~card:(Z.one) ~step:Z.zero (Z.of_int 5))  (CircularLinearProgression.create ~width:3 ~card:(Z.one |> Z.succ) ~step:Z.zero (Z.of_int 5))

  let union_regression4 = create_union_regression (CircularLinearProgression.create ~width:3 ~card:(Z.one) ~step:Z.zero (Z.of_int 5))  (CircularLinearProgression.create ~width:3 ~card:(Z.of_int 256) ~step:Z.zero (Z.of_int 5))

  
  let create_shift_right_regression  a b =  bin_op_regression a b shiftr_fill0_func CircularLinearProgression.unsigned_concretize CircularLinearProgression.Z.Set.union

  (*(((base 1)(step 0)(card 1)(width 1)), ((base 0)(step 0)(card 0)(width 1)))*)
  let unsigned_alp_regression _ = let start_clp =  CircularLinearProgression.create ~width:1 ~card:(Z.of_int 1) ~step:(Z.of_int 0) (Z.of_int 1) in
  let alps = CircularLinearProgression.unsigned_alps start_clp in assert_equal ~printer:(fun x -> List.map ~f:clp_printer x |> List.fold ~init:"" ~f:(fun accum x -> accum ^ "|"^x)) [
    create_alp ~width:1 ~card:(Z.of_int 1) ~step:(Z.of_int 0) (Z.of_int 1)
  ] alps  


  let unsigned_alp_regression2 _ = let start_clp =  CircularLinearProgression.create ~width:3 ~card:(Z.of_int 8) ~step:(Z.of_int 1) (Z.of_int 0) in
  let alps = CircularLinearProgression.unsigned_alps start_clp in assert_equal ~printer:(fun x -> List.map ~f:clp_printer x |> List.fold ~init:"" ~f:(fun accum x -> accum ^ "|"^x)) [
    create_alp ~width:3 ~card:(Z.of_int 8) ~step:(Z.of_int 1) (Z.of_int 0)
  ] alps  

(*big 

(((base 26)(step 2)(card 4)(width 5)), ((base 1)(step 2)(card 2)(width 5)))*)
  let shiftr_fill0_regression2 _ =
    let to_shift =  CircularLinearProgression.create ~width:5 ~step:(Z.of_int 2) ~card:(Z.of_int 4) (Z.of_int 26) in
    let by = CircularLinearProgression.create ~width:5 ~step:(Z.of_int 2) ~card:(Z.of_int 2) Z.one in
    let res = CircularLinearProgression.right_shift_unsigned to_shift by in 
    assert_equal ~printer:(clp_printer) (CircularLinearProgression.create ~width:5 ~step:Z.one ~card:(Z.of_int 16) Z.zero) res 





  let regression_test_shiftr_fill03 _ = 
    let to_shift =  CircularLinearProgression.create ~width:3 ~step:(Z.of_int 0) ~card:(Z.of_int 0) (Z.of_int 0) in
    let by = CircularLinearProgression.create ~width:3 ~step:(Z.of_int 1) ~card:(Z.of_int 2) Z.zero in
    let res = CircularLinearProgression.shift_right_fill1 to_shift by in 
    assert_equal ~printer:(clp_printer) (CircularLinearProgression.create ~width:3 ~step:Z.zero ~card:(Z.of_int 0) Z.zero) res 
    let test_illogical_shift _ =
       let res = z_illogical_shift ~width:11 (Z.of_int 0) 14 in
        assert_equal ~printer:Z.to_string (Z.of_int 2047) res


    let test_compute_capL_capU _ = 
      let ta = create_alp ~width:3 ~card:(Z.of_int 3) ~step:(Z.one) (Z.of_int 5) in
      let r = CircularLinearProgression.compute_capL_capU ta in
      assert_equal (Z.zero,Z.one) r


    let adition_regression_test _ = 
      let a = CircularLinearProgression.create ~width:6  ~card:Z.one ~step:Z.zero (Z.of_int 6) in
      let b = CircularLinearProgression.create ~width:6  ~card:(Z.of_int 2) ~step:Z.one (Z.of_int 63) in
      let res = CircularLinearProgression.add a b in 
      assert_equal ~printer:print_clp ( CircularLinearProgression.create ~width:6  ~card:(Z.of_int 2) ~step:Z.one (Z.of_int 5))res

    let subtraction_regression_test _ = let a = CircularLinearProgression.create ~width:11 ~step:Z.zero ~card:Z.zero Z.zero in 
      let b =  CircularLinearProgression.create ~width:11 ~step:Z.one ~card:(Z.of_int 2) (Z.of_int 3) in
      let res = CircularLinearProgression.sub a b in 
      assert_equal ~printer:print_clp ( CircularLinearProgression.create ~width:11  ~card:(Z.of_int 0) ~step:Z.zero (Z.of_int 0))res


    let create_clp (w,b,s,n) =  CircularLinearProgression.create ~width:w ~step:(Z.of_int s) ~card:(Z.of_int n) (Z.of_int b)

    let intersection_regression_test _ = let a = create_clp (11,0,1,15) in
    let b = create_clp (11,14,0,1) in 
    let res = CircularLinearProgression.intersection a b in 
    assert_equal ~printer:print_clp (create_clp (11,14,0,1)) res 

    let intersection_regression_test2 _ = let a = create_clp (3,1,1,4) in
    let b = create_clp (3,0,1,8) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    let res = CircularLinearProgression.intersection a b in 
    assert_equal ~printer:print_clp (create_clp (3,1,1,4)) res 


    let intersection_regression_test3 _ = let a = create_clp (11,855,866,45) in
    let b = create_clp (11,41,6,4) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_concrete_interseciton a b) |> print_endline ;
    let res = CircularLinearProgression.intersection a b in 
    assert_equal ~printer:print_clp (create_clp (11,47,12,2)) res 


    let intersection_regression_test4 _ = let a = create_clp (9,0,0,0) in
    let b = create_clp (9,92,122,2) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_concrete_interseciton a b) |> print_endline ;
    let res = CircularLinearProgression.intersection a b in 
    assert_equal ~printer:print_clp (create_clp (9,0,0,0)) res 


    (*(((base 20)(step 0)(card 1)(width 6)), ((base 0)(step 1)(card 2)(width 6))) *)


    let intersection_regression_test5 _ = let a = create_clp (6,20,0,1) in
    let b = create_clp (6,0,1,2) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_concrete_interseciton a b) |> print_endline ;
    let res = CircularLinearProgression.intersection a b in 
    assert_equal ~printer:print_clp (create_clp (6,0,0,0)) res 


    let intersection_regression_test6 _ = let a = create_clp (7,33,47,5) in
    let b = create_clp (7,79,1,15) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_concrete_interseciton a b) |> print_endline ;
    let res = CircularLinearProgression.intersection a b in 
    assert_equal ~printer:print_clp (create_clp (7,80,13,2)) res 


    let intersection_regression_test7 _ = let a = create_clp (7,33,47,13) in
    let b = create_clp (7,79,1,14) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_concrete_interseciton a b) |> print_endline ;
    let res = CircularLinearProgression.intersection a b in 
    assert_equal ~printer:print_clp (create_clp (7,80,5,2)) res 


    let intersection_regression_test8 _ = let a = create_clp (7,33,47,13) in
    let b = create_clp (7,79,1,15) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_concrete_interseciton a b) |> print_endline ;
    let res = CircularLinearProgression.intersection a b in 
    assert_equal ~printer:print_clp (create_clp (7,80,47,12)) res 



    let intersection_regression_test9 _ = let a = create_clp (7,1,4,2) in
    let b = create_clp (7,0,5,2) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_concrete_interseciton a b) |> print_endline ;
    let res = CircularLinearProgression.intersection a b in 
    assert_equal ~printer:print_clp (create_clp (7,5,0,11)) res



    let left_shift_regression_test _ = let a = create_clp (11,0,1,2) in
    let b = create_clp (7,14,0,1) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_left_shifts a b) |> print_endline ;
    let res = CircularLinearProgression.left_shift a b in 
    assert_equal ~printer:print_clp (create_clp (11,0,16384,11)) res


    let left_shift_regression_test2 _ = let a = create_clp (3,1,0,1) in
    let b = create_clp (3,0,1,4) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_left_shifts a b) |> print_endline ;
    let res = CircularLinearProgression.left_shift a b in 
    assert_equal ~printer:print_clp (create_clp (3,0,1,8)) res


    let left_shift_regression_test3 _ = let a = create_clp (6,49,29,2) in
    let b = create_clp (6,1,4,2) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_left_shifts a b) |> print_endline ;
    let res = CircularLinearProgression.left_shift a b in 
    assert_equal ~printer:print_clp (create_clp (6,0,2,32)) res

    let or_regression_test _ = let a = create_clp (11,0,1,3) in
    let b = create_clp (11,14,0,1) in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (compute_ors a b) |> print_endline ;
    let res = CircularLinearProgression.logor a b in 
    assert_equal ~printer:print_clp (create_clp (11,14,1,2)) res




    let regression_test ~abstract_op ~concrete_op clp1 clp2 expected =let a = create_clp clp1 in
    let b = create_clp clp2  in 
    print_endline (print_clp a);
    print_endline (print_clp b);
    "concrete_set" ^ print_set  (concrete_op a b) |> print_endline ;
    let res = abstract_op a b in 
    assert_equal ~printer:print_clp (create_clp expected) res


    let and_regression_test _ = regression_test ~abstract_op:CircularLinearProgression.logand ~concrete_op:compute_ands (11,0,1,3) (11,14,0,1) (11,0,2,2)

    let unary_regression ~abstract_op ~concrete_op c expected = 
        let a = create_clp c in 
        print_endline (print_clp a);
        "concrete_set" ^ print_set (concrete_op a) |> print_endline;
        let res = abstract_op a in 
        assert_equal ~printer:print_clp (create_clp expected)  res

    let unary_op_to_concrete_op ~op (t:  CircularLinearProgression.canon CircularLinearProgression.t) = 
      let concretes = CircularLinearProgression.unsigned_concretize t in 
      let mapped = CircularLinearProgression.Z.Set.map ~f:op  concretes in 
        mapped

    let not_comp_test a expected = 
      let c_temp = create_clp a in
      fun _ -> unary_regression ~abstract_op:CircularLinearProgression.not_clp ~concrete_op:(unary_op_to_concrete_op ~op:(fun x -> Z.erem (Z.lognot x) (CircularLinearProgression.comp_size c_temp))) a expected

    let not_comp_test1 = not_comp_test (11,0,1,3) (11,2045,1,3)

    let not_comp_test2 = not_comp_test (11,14,0,1) (11,2033,0,1)

    let and_comp_test _ = regression_test ~abstract_op:CircularLinearProgression.logand ~concrete_op:compute_ands (11,2045,1,3)   (11,2033,0,1) (11,2032,1,2)

    let not_comp_test3 = not_comp_test (11,2032,1,2) (11,14,1,2)


    let and_regression_unwrapped_compute_of_s _ = regression_test ~abstract_op:CircularLinearProgression.logand ~concrete_op:compute_ands (7,28,0,1)   (7,99,9,3) (7,0,4,6)

    let or_regression2 _ = regression_test ~abstract_op: CircularLinearProgression.logor ~concrete_op:compute_ors (12,3935,1031,6) (12,1,0,1) (12,1,0,1)



    let regression_test_shiftr_fill1 _ = regression_test ~abstract_op:CircularLinearProgression.shift_right_fill1 ~concrete_op:compute_right_shifts_fill1 (11,0,0,1) (11,14,0,1) (11,2047,0,1)
  
    
  
    let regression_test_shiftr_fill1_t2 _ = regression_test ~abstract_op:CircularLinearProgression.shift_right_fill1 ~concrete_op:compute_right_shifts_fill1 (6,1,0,1) (6,1,0,1) (6,32,0,1)
  
    let test_regression_sub_for_right_shift _ = regression_test ~abstract_op:CircularLinearProgression.sub ~concrete_op:compute_sub (6,6,0,1) (6,1,0,1) (6,5,0,1)

  

      let compute_gt clp1 clp2 =
        let c1_vals = CircularLinearProgression.signed_concretize clp1 in
        let c2_vals = CircularLinearProgression.signed_concretize clp2 in 
        let max_c2 = CircularLinearProgression.Z.Set.max_elt_exn c2_vals in
        CircularLinearProgression.Z.Set.filter ~f:(fun e -> Z.geq e max_c2) c1_vals

    let test_regression_limit_gt_signed _ = regression_test ~abstract_op: CircularLinearProgression.limit_gte_signed ~concrete_op:compute_gt (6,5,0,1) (6,0,0,1) (6,5,0,1)

  
    (*addition regfression test
    ((base 9)(step 0)(card 1)(width 9)) ((base 408)(step 218)(card 7)(width 9))
    *)


    let add_regression _ = regression_test ~abstract_op: CircularLinearProgression.add ~concrete_op:compute_adds (9,9,0,1) (9,408,218,7) (9,417,218,7)
   
    (*((base 49)(step 0)(card 1)(width 6)), ((base 1)(step 4)(card 5)(width 6)))*)
    let add_regression2 _ = regression_test ~abstract_op: CircularLinearProgression.add ~concrete_op:compute_adds (6,49,0,1) (6,1,4,5) (6,50,4,5)



    let add_regression3 _ = regression_test ~abstract_op: CircularLinearProgression.add ~concrete_op:compute_adds (11,0,1,2035) (11,14,0,1) (11,14,1,2035)


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
    "test_slow_alp_split_unsigned" >:: test_slow_alp_split_unsigned;
    test_neg;
    test_not_signed;
    test_not_unsigned;
    test_union;
    "union_regression" >:: union_regression;
    "union_regression2" >:: union_regression2;
    "test_neg_regression" >:: neg_regression; 
    "test_div_by_zero_union_regression" >:: union_regression3;
    "test_union_regression_second_div_by_zero" >:: union_regression4;
    "test_canon_0stepwitherem" >:: test_canon_0step;
    "unsigned_alp_regression" >:: unsigned_alp_regression;
    "shiftr_fill0_regression" >:: shiftr_fill0_regression;
   (*test_shiftr_fill0;*)
    test_shiftr_fill1;
    "unsigned_alp_regression2" >:: unsigned_alp_regression2;
    "shiftr_fill0_regression2" >:: shiftr_fill0_regression2;
    "regression_test_shiftr_fill03" >:: regression_test_shiftr_fill03;
    "test_compute_capL_capU" >:: test_compute_capL_capU;
    "regression_test_shiftr_fill1" >:: regression_test_shiftr_fill1; 
   "test_illogical_shift" >:: test_illogical_shift;
   "adition_regression_test" >:: adition_regression_test;
   "subtraction_regression_test" >:: subtraction_regression_test;
    test_intersection;
    test_left_shift;
   "left_shift_regression_test" >:: left_shift_regression_test;
   "left_shift_regression_test2" >:: left_shift_regression_test2;
   "intersection_regression_test" >:: intersection_regression_test;
   "intersection_regression_test2" >:: intersection_regression_test2;
   "intersection_regression_test3" >:: intersection_regression_test3; 
   "intersection_regression_test4" >:: intersection_regression_test4;
   "intersection_regression_test5" >:: intersection_regression_test5;
   "intersection_regression_test6" >:: intersection_regression_test6;
   "intersection_regression_test7" >:: intersection_regression_test7;
   "intersection_regression_test8" >:: intersection_regression_test8;
   "intersection_regression_test9" >:: intersection_regression_test9;
   "left_shift_regression_test3" >:: left_shift_regression_test3;
    test_and;
   "and_regression_test" >:: and_regression_test;
   "and_regression_unwrapped_compute_of_s" >:: and_regression_unwrapped_compute_of_s;
    "or_regression_test" >:: or_regression_test;
    "not_comp_test1" >:: not_comp_test1;
    "not_comp_test2" >:: not_comp_test2;
    "and_comp_test" >:: and_comp_test;
    "not_comp_test3" >:: not_comp_test3;
    "regression_test_shiftr_fill1_t2" >:: regression_test_shiftr_fill1_t2;
   test_or;
   test_neg;
   test_add;
   test_sub;
   "test_regression_sub_for_right_shift" >:: test_regression_sub_for_right_shift;
   "test_regression_limit_gt_signed" >:: test_regression_limit_gt_signed;
   "add_regression" >:: add_regression;
   "add_regression2" >:: add_regression2;
   "add_regression3" >:: add_regression3;
  ]

let () =
  run_test_tt_main suite
