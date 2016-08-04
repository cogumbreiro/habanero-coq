module Html = Dom_html

open List
open Printf
open String
open Stringext

let js = Js.string

let rec int_of_nat x =
    match x with
    | Cg.S n -> 1 + int_of_nat n
    | Cg.O -> 0
    ;;

let rec nat_of_int x =
    if x <= 0 then Cg.O
    else Cg.S (nat_of_int (x - 1))

(** May throw an exception *)

let _SO = "SO";;
let _WO = "WO";;
let _SW = "SW";;

let nat_of_string x = nat_of_int (int_of_string (trim x)) ;;

let string_of_nat x = string_of_int (int_of_nat x) ;;

let reg_of_string s : Cg.regmode =
    let s = trim s in
    if s = _WO then Cg.WAIT_ONLY
    else if s = _SO then Cg.SIGNAL_ONLY
    else if s = _SW then Cg.SIGNAL_WAIT
    else raise (Failure "reg_of_string")
  
let op_of_string s : Cg.op =
    match split (trim s) ' ' with
    | "async" :: x :: [] -> Cg.ASYNC (nat_of_string x)
    | "asyncPhased" :: x :: r :: [] -> Cg.ASYNC_PHASED ((nat_of_string x), (reg_of_string r))
    | "signal" :: [] -> Cg.SIGNAL
    | "wait" :: [] -> Cg.WAIT
    | "drop" :: [] -> Cg.DROP
    | "continue" :: [] -> Cg.CONTINUE
    | _ -> raise (Failure "op_of_string")
    ;;

let event_of_string s : Cg.event =
    let s = trim s in
    match split s ':' with
    | s::o::[] -> Cg.Pair (nat_of_string s, op_of_string o)
    | _ -> raise (Failure "op_of_string")

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

let rec as_list l : 'a list =
    match l with
    | Cg.Cons (x, l) ->
        x::(as_list l)
    | _ -> []

let rec from_list l =
    match l with
    | [] -> Cg.Nil
    | x::xs -> Cg.Cons (x,from_list xs)
    ;;

let trace_of_string s =
    let to_evt x : Cg.event list = 
        try [event_of_string x]
        with | Failure _ -> []
    in
    from_list (rev (flatten (List.map to_evt (split s '\n'))))

let string_of_trace t =
    let string_of_reg r =
        match r with
        | Cg.SIGNAL_ONLY -> _SO
        | Cg.SIGNAL_WAIT -> _SW
        | Cg.WAIT_ONLY -> _WO
    in
    let string_of_op o =
        match o with
        | Cg.ASYNC x -> "async " ^ (string_of_nat x)
        | Cg.ASYNC_PHASED (x, r) -> "asyncPhased " ^ (string_of_nat x) ^ " " ^ (string_of_reg r)
        | Cg.SIGNAL -> "signal"
        | Cg.WAIT -> "wait"
        | Cg.DROP -> "drop"
        | Cg.CONTINUE -> "continue"
    in
    let string_of_event e =
        match e with
        | Cg.Pair (x, o) ->
        (string_of_int (int_of_nat x)) ^ ": " ^ (string_of_op o)
    in
    concat "\n" (List.map string_of_event (as_list t))

let js_array_from_list l =
    let arr = jsnew Js.array_empty () in
    List.iteri (fun idx v -> Js.array_set arr idx v) l;
    arr

type edge = (Cg.nat, Cg.nat) Cg.prod

let rec js_of_vertex (idx:int) = js (string_of_int idx)

let js_of_vertices (vs:Cg.tid Cg.list) =
    let to_js (idx:int) (tid:int) =
        Js.Unsafe.obj [|
        ("id", Js.Unsafe.inject idx);
        ("label", Js.Unsafe.inject (js_of_vertex idx));
        ("group", Js.Unsafe.inject tid)
        |]
    in
    let rec convert idx xs =
        match xs with
        | x::xs -> to_js idx (int_of_nat x) :: (convert (idx+1) xs)
        | [] -> []
    in
    js_array_from_list (convert 0 (rev (as_list vs)))

let js_of_bool b = if b then Js._true else Js._false

type edge_type =
| FORK
| SYNC
| CONTINUE

let js_of_edges (cg:Cg.computation_graph) =
    let is_enabled b =
        Js.Unsafe.obj [| ("enabled", Js.Unsafe.inject (js_of_bool b)) |]
    in
    let to_js (t:edge_type) (e:edge) =
        match e with
        | Cg.Pair(n1,n2) ->
        Js.Unsafe.obj [|
        ("from", Js.Unsafe.inject (int_of_nat n1));
        ("to", Js.Unsafe.inject (int_of_nat n2));
        ("dashes", Js.Unsafe.inject (js_of_bool (t <> CONTINUE)));
        ("arrows", Js.Unsafe.inject (js "to"));
        ("smooth", Js.Unsafe.inject (is_enabled (t <> CONTINUE)))
        |]
    in
    let ec = List.map (to_js CONTINUE) (as_list (Cg.c_edges cg)) in
    let ej = List.map (to_js FORK) (as_list (Cg.f_edges cg)) in
    let es = List.map (to_js SYNC) (as_list (Cg.s_edges cg)) in
    js_array_from_list (ec @ ej @ es)

let js_of_cg bcg =
    match bcg with
    | Cg.Pair (b, cg) ->
    Js.Unsafe.obj [|
        ("nodes", Js.Unsafe.inject (js_of_vertices (Cg.get_nodes b)));
        ("edges", Js.Unsafe.inject (js_of_edges cg)) |]

let draw_graph container g =
    let opts = Js.Unsafe.js_expr 
 "
{
  edges: {
    width: 1,
    smooth: {
        enabled: false
    }
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

let parse_cg container t =
    match Cg.build t with
    | Cg.None -> ()
    | Cg.Some cg -> draw_graph container (js_of_cg cg)
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
    let graph =
        Js.Opt.get (Html.document##getElementById(Js.string "graph_out"))
        (fun () -> assert false) in
    let handler = (fun _ ->
        let trace_txt = Js.to_string (txt##value) in
        let t = trace_of_string trace_txt in
        (match !last_trace = t, Cg.build t with
        | false, Cg.Some cg ->
            last_trace := t;
            draw_graph graph (js_of_cg cg)
        | false, Cg.None ->
            print_string ("Parsed string:\n" ^ string_of_trace t ^ "\n")
        | _ -> ()
        );
        Js._false)
    in
    txt##onkeyup <- Html.handler handler;
    let _ = handler () in
    Js._false

let _ =
    Html.window##onload <- Html.handler onload

