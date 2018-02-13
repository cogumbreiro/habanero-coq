open Ocamlbuild_plugin

let link_C_library clib a libname env build =
  let open Outcome in
  let open Command in
  let clib = env clib and a = env a and libname = env libname in
  let objs = string_list_of_file clib in
  let include_dirs = Pathname.include_dirs_of (Pathname.dirname a) in
  let obj_of_o x =
    if Filename.check_suffix x ".o" && !Options.ext_obj <> "o" then
      Pathname.update_extension !Options.ext_obj x
    else x in
  let results = build (List.map (fun o -> List.map (fun dir -> dir / obj_of_o o) include_dirs) objs) in
  let objs = List.map begin function
    | Good o -> o
    | Bad exn -> raise exn
  end results in
  
  Cmd(S[!Options.ocamlopt; A"-o"; Px libname;
  A"-linkpkg";
  T(tags_of_pathname a++"c"++"compile");
  (* only on macosx  -ccopt -dynamiclib *) atomize objs]);;

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
      
      flag [ "compile" ; "c" ; "file:lib/libhsem.a"; "linux"] (S[A"-output-obj"; A"-runtime-variant"; A"_pic";]);
      flag [ "compile" ; "c" ; "file:lib/libhsem.a"; "windows"] (S[A"-output-obj"; ]);
      flag [ "compile" ; "c" ; "file:lib/libhsem.a"; "macos"] (S[A"-runtime-variant"; A"_pic";A"-ccopt"; A"-dynamiclib"]);

      rule "generates libhsem"
        ~dep:"%(path)lib%(libname)clib"
        ~prod:("%(path)lib%(libname)" ^ (!Options.ext_dll))
       (link_C_library "%(path)lib%(libname)clib" ("%(path)lib%(libname)" ^ !Options.ext_lib) ("%(path)lib%(libname)" ^ !Options.ext_dll))
      ;

      (* XXX: In the orignal makefile we had these flags set; not sure if actually neede. *)
      flag ["compile"; "c"; "file:hsem_stubs.c"] (S [ A"-cc"; A"gcc -fPIC";]);
      flag ["compile"; "c"; "file:init.c"] (S [ A"-cc"; A"gcc -fPIC";]);
    | _ -> ())

