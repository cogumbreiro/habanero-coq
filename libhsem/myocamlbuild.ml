open Ocamlbuild_plugin
let () =
  dispatch (function
    | Before_options ->
      Options.use_ocamlfind := true;
      Options.make_links := false;
    | After_rules -> 
      rule "cstubs: x_c_gen.native -> x_stubs_gen.c"
        ~dep:"stub_generator/generate.native"
        ~prods:["hsem.c"; "hsem.h"; "hsem_bindings.ml"]
      (fun env _build -> Cmd (S
        [A ("stub_generator/generate.native"); A ""]
        )
      );
      let shell x = run_and_read x |> String.trim in
      let ctypes_dir = shell "ocamlfind query ctypes" in
      flag ["compile"; "c"; "file:hsem.c"] (S [ A"-cc"; A"gcc -fPIC";
        A"-I"; P ctypes_dir;
      ]);
      (* XXX: generate the shared library; we need to add depedencies first *)
    | _ -> ())

