open Hsem
open Cmdliner
open Yojson.Basic.Util
open Yojson.Basic

(** Defines the command line option to parse the filename. *)
let fname =
  let doc = "Filename to parse. The file must be JSONL encoded." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FILENAME" ~doc)


(** Builds the command line UI *)
let parse_t =
  let do_parse fname =
    try (
      let s = Hsem.parse fname in
      let enqueued = Finish.checks_enqueued s in
      let running = Finish.checks_running s in
      match enqueued, running with
      | [], [] -> `Ok true
      | _, _ ->
        let js_enq = `List (List.map package_to_json enqueued) |> pretty_to_string in
        let js_run = `List (List.map (fun x -> `Int x) running) |> pretty_to_string in
        `Error (false, "There are still operations enqueued or tasks running.\nOperations enqueued: " ^ js_enq ^ "\nTasks running: " ^ js_run)
    ) with Hsem.Err e -> `Error(false, e)
  in
  Term.(ret (const do_parse $ fname))

let () = Term.exit @@ Term.eval (parse_t, Term.info "hsem")

