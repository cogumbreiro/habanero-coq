open Hsem
open Cmdliner
open Yojson.Basic.Util
open Yojson.Basic

(** Defines the command line option to parse the filename. *)
let files =
  let doc = "Filename to parse. The file must be JSONL encoded." in
  Arg.(non_empty & pos_all file [] & info [] ~docv:"FILE" ~doc)

(** Builds the command line UI *)
let parse_t =
  let do_parse fnames =
    try begin
      let f fname = try begin
        let s = Hsem.parse fname in
        let enqueued = Finish.checks_enqueued s in
        let running = Finish.checks_running s in
        match enqueued, running with
        | [], [] -> ()
        | _, _ ->
          let js_enq = `List (List.map package_to_json enqueued) |> pretty_to_string in
          let js_run = `List (List.map (fun x -> `Int x) running) |> pretty_to_string in
          raise (Hsem.Err ("There are still operations enqueued or tasks running.\nOperations enqueued: " ^ js_enq ^ "\nTasks running: " ^ js_run))
      end with Hsem.Err e ->
          raise (Hsem.Err (fname ^ ": " ^ e)) (* prefix the error with the filename *)
      in
      List.iter f fnames;
      `Ok true
    end with Hsem.Err e -> `Error(false, e)
  in
  Term.(ret (const do_parse $ files))

let () = Term.exit @@ Term.eval (parse_t, Term.info "hsem")

