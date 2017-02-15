open OUnit2;;
open Continuation_transform;;
open Ocaml_a_translator;;

let ident_test _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr x] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hgroup = None in
  let expected_start = [%expr x] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal expected actual
;;

let constant_test_1 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr 4] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hgroup = None in
  let expected_start = [%expr 4] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal expected actual
;;

let constant_test_2 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr 'a'] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hgroup = None in
  let expected_start = [%expr 'a'] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal expected actual
;;

let read_test _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr [%read]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back =
    {h_pat = [%pat? Part0];
     h_exp = [%expr next_token];
     h_type = Cont_handler} in
  let expected_others = Handler_set.empty in
  let expected_hgroup = Some {back = expected_back; others = expected_others} in
  let expected_start = [%expr Part0] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let result_test_1 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr [%result 4]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hgroup = None in
  let expected_start = [%expr Result 4] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let result_test_2 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr [%result x]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hgroup = None in
  let expected_start = [%expr Result x] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let let_test_1 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr let x = 4 in x] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hgroup = None in
  let expected_start = [%expr let var0 = 4 in let x = var0 in x] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let let_test_2 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr let x = [%read] in x] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back =
    {h_pat = [%pat? Part0];
     h_exp = [%expr let var0 = next_token in let x = var0 in x];
     h_type = Cont_handler} in
  let expected_hset = Handler_set.empty in
  let expected_hgroup = Some {back = expected_back; others = expected_hset} in
  let expected_start = [%expr Part0] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let let_test_3 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr let x = 3 in let y = [%read] in [%result (x, y)]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back =
    { h_pat = [%pat? Part0];
      h_exp = [%expr let var0 = next_token in let y = var0 in Result (x, y)];
      h_type = Cont_handler} in
  let expected_hset = Handler_set.empty in
  let expected_hgroup = Some {back = expected_back; others = expected_hset} in
  let expected_start = [%expr let var1 = 3 in let x = var1 in Part0] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let let_test_4 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr let x = [%read]
                 in let y = [%read]
                 in [%result (x,y)]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hset =
    Handler_set.singleton
      ({ h_pat = [%pat? Part0];
         h_exp = [%expr let var1 = next_token in let x = var1 in Part1];
         h_type = Cont_handler}) in
  let expected_back =
    {h_pat = [%pat? Part1];
     h_exp = [%expr let var0 = next_token in let y = var0 in Result (x, y)];
     h_type = Cont_handler}  in
  let expected_hgroup = Some {back = expected_back; others = expected_hset} in
  let expected_start = [%expr Part0] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let tuple_test_1 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr let x = (2, 3) in [%result x]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hgroup = None in
  let expected_start = [%expr let var2 =
                                (let var0 = 2 in
                                 let var1 = 3 in
                                 (var0, var1)) in
                              let x = var2 in
                              Result x] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let tuple_test_2 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr let x = (3, [%read]) in [%result x]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back =
    {h_pat = [%pat? Part0];
     h_exp = [%expr let var2 =
                      let var1 = next_token in
                      (var0, var1) in
                    let x = var2 in Result x];
     h_type = Cont_handler} in
  let expected_others = Handler_set.empty in
  let expected_hgroup = Some {back = expected_back; others = expected_others} in
  let expected_start = [%expr let var0 = 3 in Part0] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let tuple_test_3 _ =
  let context1 = Ocaml_a_translator.new_context() in
  let e = [%expr let x = ([%read], 3) in [%result x]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back =
    {h_pat = [%pat? Part0];
     h_exp = [%expr let var2 =
                      (let var0 = next_token in
                       let var1 = 3 in
                       (var0, var1))
                    in let x = var2 in
                    Result x];
     h_type = Cont_handler} in
  let expected_others = Handler_set.empty in
  let expected_hgroup =
    Some {back = expected_back; others = expected_others} in
  let expected_start = [%expr Part0] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let tuple_test_4 _ =
  let context1 = Ocaml_a_translator.new_context() in
  let e = [%expr let x = ([%read], [%read]) in [%result x]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back =
    {h_pat = [%pat? Part1];
     h_exp = [%expr let var2 =
                           (let var1 = next_token in
                            (var0, var1)) in
                         let x = var2 in
                    Result x];
     h_type = Cont_handler} in
  let h_elt =
    {h_pat = [%pat? Part0];
     h_exp = [%expr let var0 = next_token in Part1];
     h_type = Cont_handler} in
  let hset = Handler_set.singleton h_elt in
  let expected_hgroup = Some {back = expected_back; others = hset} in
  let expected_start = [%expr Part0] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

(*TODO: test construct*)

(*TODO: test apply*)

(*TODO: test record*)

(*TODO: test field*)

let ifthenelse_test_1 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr if x then 1 else 0] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hgroup = None in
  let expected_start = [%expr let var0 = x in if var0 then 1 else 0] in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected actual
;;

let ifthenelse_test_2 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr if x then [%read] else 0] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let acutal = continuation_transform a_e context2 in
  let expected_back = {h_pat = [%pat? Goto2 __varct__0];
                       h_exp = [%expr __varct__0];
                       h_type = Goto_handler} in
  let h_elt_1 = {h_pat = [%pat? Part0];
                 h_exp = [%expr Goto2 next_token];
                 h_type = Cont_handler} in
  let h_elt_2 = {h_pat = [%pat? Goto0];
                 h_exp = [%expr Part0];
                 h_type = Goto_handler} in
  let h_elt_3 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Goto2 0];
                 h_type = Goto_handler} in
  let expected_others =
    Handler_set.singleton h_elt_1
    |> Handler_set.add h_elt_2
    |> Handler_set.add h_elt_3
  in
  let expected_start = [%expr let var0 = x in if var0 then Goto0 else Goto1] in
  let expected_hgroup = Some {back = expected_back;
                         others = expected_others;} in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~printer:show_continuation_transform_result expected acutal
;;

let ifthenelse_test_3 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr if x then 0 else [%read]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back = {h_pat = [%pat? Goto2 __varct__0];
                       h_exp = [%expr __varct__0];
                       h_type = Goto_handler} in
  let h_elt_1 = {h_pat = [%pat? Part0];
                 h_exp = [%expr Goto2 next_token];
                 h_type = Cont_handler} in
  let h_elt_2 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Part0];
                 h_type = Goto_handler} in
  let h_elt_3 = {h_pat = [%pat? Goto0];
                 h_exp = [%expr Goto2 0];
                 h_type = Goto_handler} in
  let expected_others =
    Handler_set.singleton h_elt_1
    |> Handler_set.add h_elt_2
    |> Handler_set.add h_elt_3
  in
  let expected_start = [%expr let var0 = x in if var0 then Goto0 else Goto1] in
  let expected_hgroup = Some {back = expected_back;
                              others = expected_others} in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let ifthenelse_test_4 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr if x then
                   if y then [%read] else 0
                 else
                   0] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back = {h_pat = [%pat? Goto5 __varct__1];
                       h_exp = [%expr __varct__1];
                       h_type = Goto_handler} in
  let h_elt_1 = {h_pat = [%pat? Part0];
                 h_exp = [%expr Goto2 next_token];
                 h_type = Cont_handler} in
  let h_elt_2 = {h_pat = [%pat? Goto0];
                 h_exp = [%expr Part0];
                 h_type = Goto_handler} in
  let h_elt_3 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Goto2 0];
                 h_type = Goto_handler} in
  let h_elt_4 = {h_pat = [%pat? Goto2 __varct__0];
                 h_exp = [%expr Goto5 __varct__0];
                 h_type = Goto_handler} in
  let h_elt_5 = {h_pat = [%pat? Goto3];
                 h_exp = [%expr let var1 = y in
                                if var1 then Goto0 else Goto1];
                 h_type = Goto_handler} in
  let h_elt_6 = {h_pat = [%pat? Goto4];
                 h_exp = [%expr Goto5 0];
                 h_type = Goto_handler} in
  let expected_others =
    Handler_set.singleton h_elt_1
    |> Handler_set.add h_elt_2
    |> Handler_set.add h_elt_3
    |> Handler_set.add h_elt_4
    |> Handler_set.add h_elt_5
    |> Handler_set.add h_elt_6
  in
  let expected_start = [%expr let var0 = x in
                              if var0 then Goto3 else Goto4] in
  let expected_hgroup = Some {back = expected_back; others = expected_others} in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let ifthenelse_test_5 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr if x then (0, [%read]) else ([%read], 0)] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back = {h_pat = [%pat? Goto2 __varct__0];
                       h_exp = [%expr __varct__0];
                       h_type = Goto_handler} in
  let h_elt_1 = {h_pat = [%pat? Part0];
                 h_exp = [%expr Goto2 (let var4 = next_token in (var3, var4))];
                 h_type = Cont_handler} in
  let h_elt_2 = {h_pat = [%pat? Part1];
                 h_exp = [%expr Goto2 (let var0 = next_token in
                                       let var1 = 0 in
                                       (var0, var1))];
                 h_type = Cont_handler} in
  let h_elt_3 = {h_pat = [%pat? Goto0];
                 h_exp = [%expr let var3 = 0 in Part0];
                 h_type = Goto_handler} in
  let h_elt_4 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Part1];
                 h_type = Goto_handler} in
  let expected_others =
    Handler_set.singleton h_elt_1
    |> Handler_set.add h_elt_2
    |> Handler_set.add h_elt_3
    |> Handler_set.add h_elt_4
  in
  let expected_start = [%expr let var2 = x in if var2 then Goto0 else Goto1] in
  let expected_hgroup = Some {back = expected_back;
                              others = expected_others} in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let match_test_1 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr match a with
       | Foo x -> 0
       | Bar y -> 1] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back = {h_pat = [%pat? Goto0 __varct__0];
                       h_exp = [%expr __varct__0];
                       h_type = Goto_handler} in
  let h_elt_1 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Goto0 0];
                 h_type = Goto_handler} in
  let h_elt_2 = {h_pat = [%pat? Goto2];
                 h_exp = [%expr Goto0 1];
                 h_type = Goto_handler} in
  let expected_others =
    Handler_set.singleton h_elt_1
    |> Handler_set.add h_elt_2
  in
  let expected_start = [%expr let var0 = a in
                              match var0 with
                              | Foo x -> Goto1
                              | Bar y -> Goto2] in
  let expected_hgroup = Some {back = expected_back; others = expected_others} in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let match_test_2 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr match x with
       | A -> 0
       | B -> [%read]
       | C -> 1] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back = {h_pat = [%pat? Goto0 __varct__0];
                       h_exp = [%expr __varct__0];
                       h_type = Goto_handler} in
  let h_elt_1 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Goto0 0];
                 h_type = Goto_handler} in
  let h_elt_2 = {h_pat = [%pat? Goto2];
                 h_exp = [%expr Part0];
                 h_type = Goto_handler} in
  let h_elt_3 = {h_pat = [%pat? Part0];
                 h_exp = [%expr Goto0 next_token];
                 h_type = Cont_handler} in
  let h_elt_4 = {h_pat = [%pat? Goto3];
                 h_exp = [%expr Goto0 1];
                 h_type = Goto_handler} in
  let expected_others =
    Handler_set.singleton h_elt_1
    |> Handler_set.add h_elt_2
    |> Handler_set.add h_elt_3
    |> Handler_set.add h_elt_4
  in
  let expected_start =
    [%expr let var0 = x in
           match var0 with
           | A -> Goto1
           | B -> Goto2
           | C -> Goto3] in
  let expected_hgroup = Some {back = expected_back; others = expected_others} in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let match_test_3 _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr match x with
       | A -> 0
       | B -> if y then 0 else [%read]
       | C -> [%read]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back = {h_pat = [%pat? Goto0 __varct__1];
                       h_exp = [%expr __varct__1];
                       h_type = Goto_handler} in
  let h_elt_1 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Goto3 0];
                 h_type = Goto_handler} in
  let h_elt_2 = {h_pat = [%pat? Goto2];
                 h_exp = [%expr Part0];
                 h_type = Goto_handler} in
  let h_elt_3 = {h_pat = [%pat? Part0];
                 h_exp = [%expr Goto3 next_token];
                 h_type = Cont_handler} in
  let h_elt_4 = {h_pat = [%pat? Goto4];
                 h_exp = [%expr Goto0 0];
                 h_type = Goto_handler} in
  let h_elt_5 = {h_pat = [%pat? Goto5];
                 h_exp = [%expr let var1 = y in
                                if var1 then Goto1 else Goto2];
                 h_type = Goto_handler} in
  let h_elt_6 = {h_pat = [%pat? Goto6];
                 h_exp = [%expr Part1];
                 h_type = Goto_handler} in
  let h_elt_7 = {h_pat = [%pat? Part1];
                 h_exp = [%expr Goto0 next_token];
                 h_type = Cont_handler} in
  let h_elt_8 = {h_pat = [%pat? Goto3 __varct__0];
                 h_exp = [%expr Goto0 __varct__0];
                 h_type = Goto_handler} in
  let expected_others =
    List.map Handler_set.singleton [h_elt_1; h_elt_2; h_elt_3; h_elt_4; h_elt_5; h_elt_6; h_elt_7; h_elt_8]
    |> List.fold_left Handler_set.union Handler_set.empty
  in
  let expected_start =
    [%expr let var0 = x in
           match var0 with
           | A -> Goto4
           | B -> Goto5
           | C -> Goto6] in
  let expected_hgroup = Some {back = expected_back; others = expected_others} in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let sequence_test_no_reads _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr 4; true] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_hgroup = None in
  let expected_start = [%expr 4; true] in
  let expected = (expected_hgroup, expected_start) in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let sequence_test_read_first _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr [%read]; true] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_back = {h_pat = [%pat? Part0];
                       h_exp = [%expr next_token; true];
                       h_type = Cont_handler} in
  let expected_others = Handler_set.empty in
  let expected_hgroup = {back = expected_back;
                         others = expected_others} in
  let expected_start = [%expr Part0] in
  let expected = (Some expected_hgroup, expected_start) in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let sequence_test_read_second _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr 4; [%read]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_start = [%expr 4; Part0] in
  let expected_back = {h_pat = [%pat? Part0];
                       h_exp = [%expr next_token];
                       h_type = Cont_handler} in
  let expected_others = Handler_set.empty in
  let expected_hgroup = {back = expected_back;
                         others = expected_others} in
  let expected = (Some expected_hgroup, expected_start) in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let sequence_test_two_reads _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr [%read]; [%read]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_start = [%expr Part0] in
  let h_elt = {h_pat = [%pat? Part0];
               h_exp = [%expr next_token; Part1];
               h_type = Cont_handler} in
  let expected_others = Handler_set.singleton h_elt in
  let expected_back = {h_pat = [%pat? Part1];
                       h_exp = [%expr next_token];
                       h_type = Cont_handler} in
  let expected_hgroup = Some {back = expected_back;
                         others = expected_others} in
  let expected = (expected_hgroup, expected_start) in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let sequence_test_nested_three _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr 4; [%read]; true] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_start = [%expr 4; Part0] in
  let h_back = {h_pat = [%pat? Part0];
               h_exp = [%expr next_token; true];
               h_type = Cont_handler} in
  let expected_others = Handler_set.empty in
  let expected_hgroup = Some {back = h_back;
                              others = expected_others} in
  let expected = (expected_hgroup, expected_start) in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let sequence_test_nested_ifthenelse_1 _ =
  let context1 = Ocaml_a_translator.new_context() in
  let e = [%expr [%read]; if [%read] then true else false] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_start = [%expr Part0] in
  let h_elt_exp = [%expr next_token; Part1] in
  let h_elt = {h_pat = [%pat? Part0];
               h_exp = h_elt_exp;
               h_type = Cont_handler} in
  let h_back_exp = [%expr let var0 = next_token in
                            if var0 then true else false] in
  let h_back = {h_pat = [%pat? Part1];
                h_exp = h_back_exp;
                h_type = Cont_handler} in
  let h_others = Handler_set.singleton h_elt in
  let expected_hgroup = Some {back = h_back;
                              others = h_others} in
  let expected = (expected_hgroup, expected_start) in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let sequence_test_nested_gotos _ =
  let context1 = Ocaml_a_translator.new_context () in
  let e = [%expr if x then [%read] else 0;
                   match y with
                   | Foo -> 1
                   | Bar -> [%read]] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_start = [%expr let var1 = x in
                        if var1 then Goto0 else Goto1] in
  let h_elt_1 = {h_pat = [%pat? Goto0];
                 h_exp = [%expr Part0];
                 h_type = Goto_handler} in
  let h_elt_2 = {h_pat = [%pat? Part0];
                 h_exp = [%expr Goto2 next_token];
                 h_type = Cont_handler} in
  let h_elt_3 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Goto2 0];
                 h_type = Goto_handler} in
  let h_elt_4 = {h_pat = [%pat? Goto2 __varct__0];
                 h_exp = [%expr __varct__0;
                 let var0 = y in
                 match var0 with
                 | Foo -> Goto4
                 | Bar -> Goto5];
                 h_type = Goto_handler} in
  let h_elt_5 = {h_pat = [%pat? Goto4];
                 h_exp = [%expr Goto3 1];
                 h_type = Goto_handler} in
  let h_elt_6 = {h_pat = [%pat? Goto5];
                 h_exp = [%expr Part1];
                 h_type = Goto_handler} in
  let h_elt_7 = {h_pat = [%pat? Part1];
                 h_exp = [%expr Goto3 next_token];
                 h_type = Cont_handler} in
  let h_back = {h_pat = [%pat? Goto3 __varct__1];
                h_exp = [%expr __varct__1];
                h_type = Goto_handler} in
  let expected_others =
    List.map Handler_set.singleton [h_elt_1; h_elt_2; h_elt_3; h_elt_4; h_elt_5; h_elt_6; h_elt_7]
    |> List.fold_left Handler_set.union Handler_set.empty
  in
  let expected_hgroup = Some {back = h_back;
                              others = expected_others} in
  let expected = (expected_hgroup, expected_start) in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let try_test_1 _ =
  let context1 = Ocaml_a_translator.new_context() in
  let e = [%expr
    try
      5
    with
    | _ -> 0
  ] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_start = [%expr
    try
      Goto0 5
    with
    | _ -> Goto1
  ] in
  let expected_back = {h_pat = [%pat? Goto0 __varct__0];
                       h_exp = [%expr __varct__0];
                       h_type = Goto_handler} in
  let h_elt_1 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Goto0 0];
                 h_type = Goto_handler} in
  let expected_others = Handler_set.singleton h_elt_1 in
  let expected_hgroup = Some {back = expected_back;
                              others = expected_others} in
  let expected = (expected_hgroup, expected_start) in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let try_test_2 _ =
  let context1 = Ocaml_a_translator.new_context() in
  let e = [%expr
    try
      (6, [%read])
    with
    | A -> 0
    | B -> 1
  ] in
  let a_e = a_translator e context1 in
  let context2 = Continuation_transform.new_context () in
  let actual = continuation_transform a_e context2 in
  let expected_start =
    [%expr
      try
        let var0 = 6 in
        Part0
      with
      | A -> Goto1
      | B -> Goto2
    ] in
  let h_e_elt_exp =
    [%expr
      try
        Goto0 (let var1 = next_token in
               (var0, var1))
      with
      | A -> Goto1
      | B -> Goto2
    ] in
  let h_e_elt = {h_pat = [%pat? Part0];
                 h_exp = h_e_elt_exp;
                 h_type = Cont_handler} in
  let h_elt_1 = {h_pat = [%pat? Goto1];
                 h_exp = [%expr Goto0 0];
                 h_type = Goto_handler} in
  let h_elt_2 = {h_pat = [%pat? Goto2];
                 h_exp = [%expr Goto0 1];
                 h_type = Goto_handler} in
  let h_back = {h_pat = [%pat? Goto0 __varct__0];
                h_exp = [%expr __varct__0];
                h_type = Goto_handler} in
  let h_others =
    List.map Handler_set.singleton [h_elt_1; h_elt_2; h_e_elt]
    |> List.fold_left Handler_set.union Handler_set.empty in
  let expected_hgroup = Some {back = h_back;
                              others = h_others} in
  let expected = (expected_hgroup, expected_start)
  in
  assert_equal ~cmp:equal_continuation_transform_result ~printer:show_continuation_transform_result expected actual
;;

let tests = "Continuation_transform" >::: [

    "ident test" >:: ident_test;
    "constant test 1" >:: constant_test_1;
    "constant test 2" >:: constant_test_2;
    "read test" >:: read_test;
    "result test 1" >:: result_test_1;
    "result test 2" >:: result_test_2;
    "let test 1" >:: let_test_1;
    "let test 2" >:: let_test_2;
    "let test 3" >:: let_test_3;
    "let test 4" >:: let_test_4;
    "tuple test 1" >:: tuple_test_1;
    "tuple test 2" >:: tuple_test_2;
    "tuple test 3" >:: tuple_test_3;
    "tuple test 4" >:: tuple_test_4;
    "ifthenelse test 1" >:: ifthenelse_test_1;
    "ifthenelse test 2" >:: ifthenelse_test_2;
    "ifthenelse test 3" >:: ifthenelse_test_3;
    "ifthenelse test 4" >:: ifthenelse_test_4;
    "ifthenelse test 5" >:: ifthenelse_test_5;
    "match test 1" >:: match_test_1;
    "match test 2" >:: match_test_2;
    "match test 3" >:: match_test_3;
    "sequence test no reads" >:: sequence_test_no_reads;
    "sequence test read first" >:: sequence_test_read_first;
    "sequence test read second" >:: sequence_test_read_second;
    "sequence test two reads" >:: sequence_test_two_reads;
    "sequence test nested three" >:: sequence_test_nested_three;
    "sequence test nested if then else 1" >:: sequence_test_nested_ifthenelse_1;
    "sequence test nested gotos" >:: sequence_test_nested_gotos;
    "try test 1" >:: try_test_1;
    "try test 2" >:: try_test_2;
  ]
;;
