let () =
  Migrate_parsetree.Driver.register ~name:"pdr-programming.ppx"
    Migrate_parsetree.Versions.ocaml_406 (fun _config _cookies ->
        Mapper.mapper)
;;
