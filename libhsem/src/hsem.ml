(* Define a struct of callbacks (C function pointers) *)
open Finish
open List

let all_ops = [
  ("INIT", PKG_INIT);
  ("BEGIN_FINISH", PKG_BEGIN_FINISH);
  ("END_FINISH", PKG_END_FINISH);
  ("BEGIN_TASK", PKG_BEGIN_TASK);
  ("END_TASK", PKG_END_TASK)
]

exception Err of string

let string_to_op (o:string) : package_op = List.find (fun x -> fst x = o) all_ops |> snd
let op_to_string (o:package_op) : string = List.find (fun x -> snd x = o) all_ops |> fst

let err_line_prefix lineno = match lineno with
  | Some l -> "Error at line #" ^ string_of_int l ^ ": "
  | None -> ""

let json_to_package j lineno =
  let open Yojson.Basic.Util in
  let do_err msg = raise (Err (err_line_prefix lineno ^ msg)) in
  let s_member k (obj:Yojson.Basic.json) = match obj with
    | `Assoc l ->
      begin
        try
          List.find (fun x -> fst x = k) l |> snd
        with
          Not_found -> do_err ("JSON key '" ^ k ^ "' was not found.")
      end
    | _ -> do_err ("Expected a JSON object, bug got: " ^ Yojson.Basic.pretty_to_string obj)
  in
  try begin
    let o : string = s_member "op" j |> to_string in
    let replace_null d j = match j with
      | `Null -> d
      | _ -> j
    in
    try {
      pkg_task = s_member "task" j |> to_int;
      pkg_op = string_to_op o;
      pkg_id = s_member "id" j |> to_int;
      pkg_time = s_member "time" j |> to_int;
      pkg_args = member "args" j |> replace_null (`List []) |> to_list |> List.map to_int;
      pkg_lineno = lineno
    } with Not_found ->
      do_err ("Unknown operation " ^ o)
  end with Type_error (e,_) ->
    do_err e

let package_to_json p =
  let open Yojson.Basic.Util in
  let lineno = match p.pkg_lineno with
    | Some x -> `Int x
    | _ -> `Null
  in
  `Assoc [
    "task", `Int (pkg_task p);
    "op", `String (op_to_string (pkg_op p));
    "id", `Int (pkg_id p);
    "time", `Int (pkg_time p);
    "args", `List (pkg_args p |> List.map (fun x -> `Int x));
    "lineno", lineno
  ]

let package_to_string p = package_to_json p |> Yojson.Basic.pretty_to_string

let run_err_to_string (r:Finish.checks_err) : string =
  let pkg_parse_err_to_string e = "Invalid arguments. " ^
    match e with
    | PKG_PARSE_NOARGS_EXPECTED -> "Expected 0 arguments."
    | PKG_PARSE_TASK_EXPECTED -> "Expected 1 task identifier."
  in
  let reduces_err_to_string (e:Finish.reduces_err) = match e with
    | TASK_EXIST x -> "Expecting task " ^ string_of_int x ^ " to be new, but it already exists."
    | TASK_NOT_EXIST x -> "Task " ^ string_of_int x ^ " does not exist."
    | FINISH_EXIST x -> "Expecting finish " ^ string_of_int x ^ " to be new, but it already exists."
    | FINISH_NOT_EXIST x -> "Finish " ^ string_of_int x ^ " does not exist."
    | FINISH_NONEMPTY x -> "Invoked END_FINISH, but finish " ^ string_of_int x ^ " is not empty."
    | FINISH_OPEN_EMPTY -> "Invoked END_FINISH, but there are 0 open finish scopes."
  in
  let (l, msg) = match r with
    | CHECKS_PARSE_TRACE_ERROR (p, e) ->
      begin
        let args : string = Yojson.Basic.pretty_to_string (`List (pkg_args p |> List.map (fun x -> `Int x))) in
        (p.pkg_lineno, pkg_parse_err_to_string e ^ " Obtained: " ^ args)
      end
    | CHECKS_REDUCES_N_ERROR (p, e) -> (p.pkg_lineno, reduces_err_to_string e ^ "\n" ^ package_to_string p)
    | CHECKS_INTERNAL_ERROR -> (None, "Unexpected internal error.")
  in
  err_line_prefix l ^ msg

let parse (filename:string) =
  let stream_file c = Stream.from (fun _ ->
     try Some (input_line c) with End_of_file -> None) in
  let chk = ref Finish.checks_make in (* initialize hchecks *)
  let chan = open_in filename in
  let lineno = ref 0 in
  let do_iter line =
    lineno := !lineno + 1;
    let line = String.trim line in
    if (line <> "") && (String.get line 0 <> '#') then begin
      try begin
        let j = Yojson.Basic.from_string line in
        let pkg = json_to_package j (Some !lineno)  in
        match Finish.checks_add pkg !chk with
        | Inl s' -> chk := s'
        | Inr e -> raise (Err (run_err_to_string e))
      end with Yojson.Json_error e -> raise (Err(err_line_prefix (Some !lineno) ^ e))
    end
  in
  Stream.iter do_iter (stream_file chan);
  close_in chan;
  !chk

