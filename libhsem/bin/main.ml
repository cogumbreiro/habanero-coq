open Hsem
open Cmdliner

let fname =
  let doc = "Filename to parse. The file must be JSONL encoded." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FILENAME" ~doc)

let parse_t = Term.(const Hsem.parse $ fname)

(*
let info = 
  let doc = "Check if a Habanero-Semantics trace is valid." in
  let man = [
    `S Manpage.s_bugs;
(*    `P "Email bug reports to <hehey at example.org>."*) ]
  in
  Term.info "chorus" ~version:"%‌%VERSION%%" ~doc ~exits:Term.default_exits ~man
*)

let () = Term.exit @@ Term.eval (parse_t, Term.info "hsem")
(*
let () =
    if Array.length Sys.argv == 2 then(
        Hsem.parse (Sys.argv.(1));
        ()
    )else
        print_string "Usage: hsem <FILENAME>\n";
        exit 0;;
        *)
