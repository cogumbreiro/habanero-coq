open Ocamlbuild_plugin

let command_output cmd =
  let ic = Unix.open_process_in cmd in
  let output = input_line ic in
  let () = close_in ic in
  String.trim output

(* Taken from: https://gist.github.com/AltGr/5bfc8cea6f01e74b95de79ceaba39369 *)
let os =
  match Sys.os_type with
  | "Unix" -> (match String.lowercase_ascii (command_output "uname -s") with
      | "darwin" -> "macos"
      | s -> s)
  | s -> String.lowercase_ascii s

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
  let extra = match os with
  | "linux" -> (S[A"-output-obj"; A"-runtime-variant"; A"_pic";])
  | "macos" -> (S[A"-runtime-variant"; A"_pic";A"-ccopt"; A"-dynamiclib"])
  | "win32" -> (S[A"-output-obj"; ])
  | _ -> (S[])
  in
  Cmd(S[!Options.ocamlopt; A"-o"; Px libname; A"-linkpkg"; extra;
    (* it's important to append 'c' and 'compile' so that tags_of_pathname
       generates all the -package fragments, which are essential to build. *)
    T(tags_of_pathname a++"c"++"compile"); atomize objs])

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
        ~prods:[
          gen_dir ^ "/hsem_stubs.c";
          gen_dir ^ "/hsem.h";
          gen_dir ^ "/hsem_bindings.ml"
        ]
      (fun env _build -> Seq [
          Cmd (S [A "mkdir"; A"-p"; A (env gen_dir)]);
          Cmd (S [A (env generator); A (env gen_dir)]);
        ]
      );
      (* Try to use pkg-config to figure out the linking path of libffi *)
      if Sys.os_type = "Unix" then begin
        try
          flag ["link"; "file:codegen/generate.native"]
               (S [A"-cclib"; A(command_output "pkg-config --libs libffi")]);
        with End_of_file -> ()
      end;
      (* `apply_bindings.ml` has a dynamic dependency on a generated file `hsem_bindings.ml`. *)
      (* 1. ensure that we compile `hsem_bindings` before compiling `apply_bindings.ml` *)
      dep ["ocaml"; "compile"; "file:lib/apply_bindings.ml"] [gen_dir ^ "/hsem_bindings.cmx"];
      (* 2. ensure that the compiler is aware of the code generator directory,
            so that it can see the generated file. *)
      flag ["ocaml"; "compile"; "file:lib/apply_bindings.ml"] (S [A"-I"; A gen_dir]);
      print_string ("EXT LIB: " ^ !Options.ext_dll ^ "\n");
      (* Rule to generate libhsem.so, which just delegates to link_C_library: *)
      rule "generates libhsem"
        ~dep:"%(path)lib%(libname)clib"
        ~prod:("%(path)lib%(libname)" ^ (!Options.ext_dll))
       (link_C_library "%(path)lib%(libname)clib" ("%(path)lib%(libname)" ^ !Options.ext_lib) ("%(path)lib%(libname)" ^ !Options.ext_dll))
      ;

    | _ -> ())

