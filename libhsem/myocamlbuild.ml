open Ocamlbuild_plugin

let () =
  dispatch (function
    | Before_options ->
      Options.use_ocamlfind := true;
      Options.make_links := false;
    | After_rules ->
      (* Rules to use our code generator (which is implicitly built)
         to genreate the ctypes stubs/bindings and the C header. *)
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
      (* `apply_bindings.ml` has a dynamic dependency on a generated file `hsem_bindings.ml`. *)
      (* 1. ensure that we compile `hsem_bindings` before compiling `apply_bindings.ml` *)
      dep ["ocaml"; "compile"; "file:lib/apply_bindings.ml"] [gen_dir ^ "/hsem_bindings.cmx"];
      (* 2. ensure that the compiler is aware of the code generator directory,
            so that it can see the generated file. *)
      flag ["ocaml"; "compile"; "file:lib/apply_bindings.ml"] (S [A"-I"; A gen_dir]);

      (* XXX: In the orignal makefile we had these flags set; not sure if actually neede. *)
      flag ["compile"; "c"; "file:hsem_stubs.c"] (S [ A"-cc"; A"gcc -fPIC";]);
      flag ["compile"; "c"; "file:init.c"] (S [ A"-cc"; A"gcc -fPIC";]);
    | _ -> ())

