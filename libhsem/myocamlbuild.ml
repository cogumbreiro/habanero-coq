open Ocamlbuild_plugin

let () =
  dispatch (function
    | Before_options ->
      Options.use_ocamlfind := true;
      Options.make_links := false;
    | After_rules ->
      let generator = "support/generate.native" in
      rule "generates ctypes stubs"
        ~dep:generator
        ~prods:["hsem_stubs.c"; "hsem.h"; "hsem_bindings.ml"]
      (fun env _build -> Cmd (S
        [A (env generator); A (env "")]
        )
      );
      ocaml_lib "src/base";
      flag ["compile"; "c"; "file:hsem_stubs.c"] (S [ A"-cc"; A"gcc -fPIC";]);

      rule "generate c"
        ~deps:["%.c"]
        ~prod:"%.exe"
      (fun env _build -> (Cmd (S [ A"gcc"; A"-o"; A (env "%.exe"); A"-I"; A"."; A"-lhsem"; A"-L"; A"."; A (env "%.c"); ])));
(*      let shell x = run_and_read x |> String.trim in *)

      rule "generates shared object"
        ~deps:["init.o"; "hsem_stubs.o"; "finish.cmx"; "hsem.cmx"; "apply_bindings.cmx"]
        ~prod:"%.so"
      (fun env _build -> Cmd (S
        [!Options.ocamlopt; A"-o"; P"libhsem.so" ]
        )
      );
        (*
      dep ["compile"; "c"; "file:libhsem.so"]
            ["init.o"; "hsem.o"];*)
      (* XXX: generate the shared library; we need to add depedencies first *)
    | _ -> ())

