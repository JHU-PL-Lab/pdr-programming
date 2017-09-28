type fresh_variable_context =
  { fvc_counter : int ref;
  fvc_prefix : string }
;;

let new_fresh_variable_context ?prefix:(prefix="__var_") () =
  { fvc_counter = ref 0;
    fvc_prefix = prefix }
;;

let fresh_variable_name_counter = ref 0;;

let fresh_variable_name fvc =
  let n = !(fvc.fvc_counter) in
  fvc.fvc_counter := n + 1;
  fvc.fvc_prefix ^ string_of_int n
;;
