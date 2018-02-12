open Ocamlbuild_plugin

let () =
  dispatch (function
    | Before_options ->
      Options.use_ocamlfind := true;
      Options.make_links := false;
    | After_rules ->
      let generator = "codegen/generate.native" in
      let gen_dir = "generated" in
      rule "generates ctypes stubs"
        ~dep:generator
        ~prods:[gen_dir ^ "/hsem_stubs.c"; gen_dir ^ "/hsem.h"; gen_dir ^ "/hsem_bindings.ml"]
      (fun env _build -> Seq[
          Cmd (S [A "mkdir"; A"-p"; A (env gen_dir)]);
          Cmd (S [A (env generator); A (env gen_dir)]);
        ]
      );
      dep ["ocaml"; "compile"; "file:lib/apply_bindings.ml"] [gen_dir ^ "/hsem_bindings.cmx"];
      flag ["ocaml"; "compile"; "file:lib/apply_bindings.ml"] (S [A"-I"; A gen_dir]);

      ocaml_lib "src/base";
      flag ["compile"; "c"; "file:hsem_stubs.c"] (S [ A"-cc"; A"gcc -fPIC";]);
      flag ["compile"; "c"; "file:init.c"] (S [ A"-cc"; A"gcc -fPIC";]);
    | _ -> ())

