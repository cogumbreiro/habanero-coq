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
    | "async" :: x :: [] -> Cg.ASYNC (int_of_string x)
    | "reg" :: x :: r :: [] -> Cg.ASYNC_PHASED ((int_of_string x), (reg_of_string r))
    | "signal" :: [] -> Cg.SIGNAL
    | "wait" :: [] -> Cg.WAIT
    | "drop" :: [] -> Cg.DROP
    | "continue" :: [] -> Cg.CONTINUE
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
    | Cg.ASYNC x -> "async " ^ (string_of_int x)
    | Cg.ASYNC_PHASED (x, r) -> "reg " ^ (string_of_int x) ^ " " ^ (string_of_reg r)
    | Cg.SIGNAL -> "signal"
    | Cg.WAIT -> "wait"
    | Cg.DROP -> "drop"
    | Cg.CONTINUE -> "continue"
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

let js_array_from_list l =
    let arr = jsnew Js.array_empty () in
    List.iteri (fun idx v -> Js.array_set arr idx v) l;
    arr

let js_array a =
    let arr = jsnew Js.array_empty () in
    Array.iteri (fun idx v -> Js.array_set arr idx v) a;
    arr

let js_of_vertex (idx:int) (ns:Cg.op Cg.MN.t) =
    js (
        match Cg.MN.find idx ns with
        | Some o -> string_of_op o
        | _ -> ""
    )

let js_of_vertices (vs:int array) (ns:Cg.op Cg.MN.t) =
    let parent_of = I.create 10 in
    List.iter (fun p ->
        match p with
        | (n_idx, Cg.ASYNC_PHASED (y,_)) ->
            I.add parent_of y (Array.get vs n_idx)
        | (n_idx, Cg.ASYNC y) ->
            I.add parent_of y (Array.get vs n_idx)
        | _ -> ()
    ) (Cg.MN.elements ns);
    let tbl = I.create 10 in
    let parent_offset tid = (try (I.find tbl (I.find parent_of tid) - 1) with | _ -> 0) in
    let to_js idx tid =
        let offset = (try (I.find tbl tid) + 1 with | _ -> parent_offset tid) in
        I.add tbl tid offset;
        Js.Unsafe.obj [|
        ("id", Js.Unsafe.inject idx);
        ("y", Js.Unsafe.inject (tid * 150));
        ("x", Js.Unsafe.inject (tid * 50 + offset * 150));
        ("label", Js.Unsafe.inject (js_of_vertex idx ns));
        ("group", Js.Unsafe.inject tid)
        |]
    in
    js_array (Array.mapi to_js vs)

let js_of_bool b = if b then Js._true else Js._false

type edge_type =
| FORK
| SYNC
| CONTINUE

let js_of_edges (cg:Cg.computation_graph) =
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
    js_array_from_list (ec @ ej @ es)

let js_of_cg (b,cg) =
    let tids = Array.of_list (rev (Cg.get_nodes b)) in
    Js.Unsafe.obj [|
        ("nodes", Js.Unsafe.inject (js_of_vertices tids (Cg.node_to_op b)));
        ("edges", Js.Unsafe.inject (js_of_edges cg)) |]

let draw_graph container g : unit =
    let opts = Js.Unsafe.js_expr 
 "
{
  edges: {
    width: 2,
    smooth: {
  type: 'vertical'
    },
    shadow:true
  },
  nodes : {
    shape: 'dot',
    size: 10,
    shadow:true,
    font: {face:'courier', size: 20, strokeWidth:3, strokeColor:'#ffffff'}
  },
  layout: {
    randomSeed: 0
  },
  physics: {
    enabled: false
  }
}"
    in
    let _ = Js.Unsafe.new_obj (Js.Unsafe.variable "vis.Network")
    [| Js.Unsafe.inject container;  Js.Unsafe.inject g; opts|] in
    ()

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
    let graph =
        Js.Opt.get (Html.document##getElementById(Js.string "graph_out"))
        (fun () -> assert false) in
    let handler = (fun _ ->
        let trace_txt = Js.to_string (txt##value) in
        let t = trace_of_string trace_txt in
        if !last_trace <> t then (
            last_trace := t;
            match Cg.build t with
            | Some cg -> draw_graph graph (js_of_cg cg)
            | None -> print_string ("Parsed string:\n" ^ string_of_trace t ^ "\n")
        ) else ();
        Js._false)
    in
    txt##onkeyup <- Html.handler handler;
    let _ = handler () in
    Js._false

let _ =
    Html.window##onload <- Html.handler onload

