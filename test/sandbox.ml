let main () =
  [%expr f 4]
  |> A_normalizer.a_translate
  |> Pprintast.string_of_expression
  |> print_endline
;;

main ();;
