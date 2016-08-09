module Html = Dom_html

open List
open Printf
open String
open Stringext

let js = Js.string

module IntHash =
    struct
        type t = int
        let equal i j = i=j
        let hash i = i land max_int
    end

module I = Hashtbl.Make(IntHash)

let _REG = "reg"
let _SO = "SO";;
let _WO = "WO";;
let _SW = "SW";;

let reg_of_string s : Cg.regmode =
    let s = trim s in
    if s = _WO then Cg.WAIT_ONLY
    else if s = _SO then Cg.SIGNAL_ONLY
    else if s = _SW then Cg.SIGNAL_WAIT
    else raise (Failure "reg_of_string")
  
let op_of_string s : Cg.op =
    match split (trim s) ' ' with
    | "reg" :: x :: r :: [] -> Cg.REGISTER { Cg.get_task = int_of_string x; Cg.get_mode = reg_of_string r }
    | "signal" :: [] -> Cg.SIGNAL
    | "wait" :: [] -> Cg.WAIT
    | "drop" :: [] -> Cg.DROP
    | _ -> raise (Failure "op_of_string")
    ;;

let event_of_string s : Cg.event =
    let s = trim s in
    match split s ':' with
    | s::o::[] -> (int_of_string s, op_of_string o)
    | _ -> raise (Failure "op_of_string")

let string_of_reg r =
    match r with
    | Cg.SIGNAL_ONLY -> _SO
    | Cg.SIGNAL_WAIT -> _SW
    | Cg.WAIT_ONLY -> _WO;;

let string_of_op o =
    match o with
    | Cg.REGISTER r -> "reg " ^ (string_of_int (Cg.get_task r)) ^ " " ^ (string_of_reg (Cg.get_mode r))
    | Cg.SIGNAL -> "signal"
    | Cg.WAIT -> "wait"
    | Cg.DROP -> "drop"
    ;;

let string_of_event e =
    match e with
    | (x, o) -> (string_of_int x) ^ ": " ^ (string_of_op o)
    ;;

let string_of_trace t =
    concat "\n" (List.map string_of_event (rev t))


let filter_duplicates lst =
  let rec is_member n mlst =
    match mlst with
    | [] -> false
    | h::tl ->
        begin
          if h=n then true
          else is_member n tl
        end
  in
  let rec loop lbuf =
    match lbuf with
    | [] -> []
    | h::tl ->
        begin
        let rbuf = loop tl
        in
          if is_member h rbuf then rbuf
          else h::rbuf
        end
  in
  loop lst

let trace_of_string s =
    let to_evt x : Cg.event list = 
        try [event_of_string x]
        with | Failure _ -> []
    in
    rev (flatten (List.map to_evt (split s '\n')))

let js_array a =
    let arr = jsnew Js.array_empty () in
    Array.iteri (fun idx v -> Js.array_set arr idx v) a;
    arr

let string_of_taskview v =
    "sp: " ^ string_of_int (Cg.signal_phase v) ^
    "\nwp: " ^ string_of_int (Cg.wait_phase v) ^
    "\nmode: " ^ string_of_reg (Cg.mode v)

type node_type =
    | Past of Cg.op
    | Current of Cg.taskview

let get_node_type (tid:int) (idx:int) (ns:Cg.op Cg.MN.t) (ph:Cg.phaser option) =
    match Cg.MN.find idx ns with
    | Some o -> Some (Past o)
    | _ ->
        (match ph with
        | Some ph -> (
            match Cg.Map_TID.find tid ph with
            | Some v -> Some (Current v)
            | _ -> None
            )
        | _ -> None)

let js_of_node_type (nt:node_type option) =
    js (
        match nt with
        | Some (Past o) -> string_of_op o
        | Some (Current v) -> "\n\n" ^ string_of_taskview v
        | _ -> ""
    )

let js_of_vertices (vs:int array) (ns:Cg.op Cg.MN.t) (ph:Cg.phaser option) =
    let parent_of = I.create 10 in
    List.iter (fun p ->
        match p with
        | (n_idx, Cg.REGISTER r) ->
            I.add parent_of (Cg.get_task r) (Array.get vs n_idx)
        | _ -> ()
    ) (Cg.MN.elements ns);
    let tbl = I.create 10 in
    let parent_offset tid = (try (I.find tbl (I.find parent_of tid) - 1) with | _ -> 0) in
    let to_js idx tid =
        let nt = get_node_type tid idx ns ph in
        let font =
            match nt with
            | Some (Current v) -> Js.Unsafe.js_expr "{strokeColor: 'yellow'}"
            | _ -> Js.Unsafe.js_expr "{}"
        in
        let offset = (try (I.find tbl tid) + 1 with | _ -> parent_offset tid) in
        I.add tbl tid offset;
        Js.Unsafe.obj [|
        ("id", Js.Unsafe.inject idx);
        ("y", Js.Unsafe.inject (tid * 150));
        ("x", Js.Unsafe.inject (tid * 50 + offset * 150));
        ("label", Js.Unsafe.inject (js_of_node_type nt));
        ("group", Js.Unsafe.inject tid);
        ("font", Js.Unsafe.inject font)
        |]
    in
    Array.mapi to_js vs

let js_of_bool b = if b then Js._true else Js._false

type edge_type =
| FORK
| SYNC
| CONTINUE

let js_of_edges (cg:Cg.computation_graph) : 'a array =
    let is_enabled b =
        Js.Unsafe.obj [| ("enabled", Js.Unsafe.inject (js_of_bool b)) |]
    in
    let js_dash t =
        match t with
        | SYNC -> js_of_bool true
        | FORK -> Js.Unsafe.js_expr "[1,10,1,10]"
        | CONTINUE -> js_of_bool false
    in
    let to_js (t:edge_type) (n1,n2) =
        Js.Unsafe.obj [|
        ("from", Js.Unsafe.inject n1);
        ("to", Js.Unsafe.inject n2);
        ("dashes", Js.Unsafe.inject (js_dash t));
        ("arrows", Js.Unsafe.inject (js "to"));
        ("smooth", Js.Unsafe.inject (is_enabled (t <> CONTINUE)))
        |]
    in
    let ec = List.map (to_js CONTINUE) (Cg.c_edges cg) in
    let ej = List.map (to_js FORK) (Cg.f_edges cg) in
    let es = List.map (to_js SYNC) (Cg.s_edges cg) in
    Array.of_list (ec @ ej @ es)

let js_of_cg (b,cg) ph =
    let tids = Array.of_list (rev (Cg.get_nodes b)) in
    (js_of_vertices tids (Cg.node_to_op b) ph, js_of_edges cg)

let js_new_network container (vs, es) =
    let js_graph = 
        Js.Unsafe.obj [|
            ("nodes", Js.Unsafe.inject (js_array vs));
            ("edges", Js.Unsafe.inject (js_array es))
        |]
    in
    let _ = Js.Unsafe.new_obj (Js.Unsafe.variable "vis.Network")
    [| Js.Unsafe.inject container; 
       Js.Unsafe.inject js_graph;
       Js.Unsafe.variable "OPTS"|] in
    ()

let string_of_phaser ph =
    let string_of_entry (t, v) =
        string_of_int t ^ ": " ^ string_of_taskview v
    in
    "{\n" ^
    String.concat ",\n" (List.map string_of_entry (Cg.Map_TID.elements ph)) ^
    "\n}"
    ;;

let onload _ =
    let txt =
        Dom_html.getElementById "trace_in"
        |> Dom_html.CoerceTo.textarea
        |> fun opt ->
        Js.Opt.case opt 
        (fun () -> assert false)
        (fun div -> div)
    in
    let last_trace = ref (trace_of_string "") in
    let trace_out =
        Js.Opt.get (Html.document##getElementById(Js.string "graph_out"))
        (fun () -> assert false) in

    js_new_network trace_out ([||], [||]);
    let handler = (fun _ ->
        let trace_txt = Js.to_string (txt##value) in
        let t = trace_of_string trace_txt in
        if !last_trace <> t then (
            last_trace := t;
            match Cg.build t with
            | Some bcg -> (
                let ph = Cg.eval_trace t in
                js_new_network trace_out (js_of_cg bcg ph)
            )
            | None -> print_string ("Parsed string:\n" ^ string_of_trace t ^ "\n")
        ) else ();
        Js._false)
    in
    txt##onkeyup <- Html.handler handler;
    let _ = handler () in
    Js._false

let _ =
    Html.window##onload <- Html.handler onload

