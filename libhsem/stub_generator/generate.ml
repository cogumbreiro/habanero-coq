(** A driver for stub generation.  Build OCaml and C code from the
    Bindings.Stubs functor. *)

let generate dirname =
  let prefix = "hsem" in
  let path basename = Filename.concat dirname basename in
  let ml_fd = open_out (path "hsem_bindings.ml") in
  let c_fd = open_out (path "hsem.c") in
  let h_fd = open_out (path "hsem.h") in
  let stubs = (module Bindings.Stubs : Cstubs_inverted.BINDINGS) in
  begin
    (* Generate the ML module that links in the generated C. *)
    Cstubs_inverted.write_ml 
      (Format.formatter_of_out_channel ml_fd) ~prefix stubs;

    (* Generate the C source file that exports OCaml functions. *)
    Format.fprintf (Format.formatter_of_out_channel c_fd)
      "#include \"hsem.h\"@\n%a"
      (Cstubs_inverted.write_c ~prefix) stubs;

    (* Generate the C header file that exports OCaml functions. *)
    Cstubs_inverted.write_c_header 
      (Format.formatter_of_out_channel h_fd) ~prefix stubs;

  end;
  close_out h_fd;
  close_out c_fd;
  close_out ml_fd

let () = generate (Sys.argv.(1))
