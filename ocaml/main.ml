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

let nat_of_string x =
  nat_of_int (int_of_string (trim x))
;;
  
let op_of_string s =
    try (
        let s = String.uppercase (trim s) in
        match split s ' ' with
        | "ASYNC" :: x :: [] -> Some (Cg.ASYNC (nat_of_string x))
        | "PHASED" :: x :: [] -> Some (Cg.ASYNC_PHASED (nat_of_string x))
        | "SIGNAL" :: ph :: [] -> Some (Cg.SIGNAL (nat_of_string ph))
        | "WAIT" :: ph :: [] -> Some (Cg.WAIT (nat_of_string ph))
        | "DROP" :: ph :: [] -> Some (Cg.DROP (nat_of_string ph))
        | "CONTINUE" :: [] -> Some Cg.CONTINUE
        | _ -> None
    ) with | _ -> None
    ;;


let event_of_string s : Cg.event option =
    let s = trim s in
    try (
        match split s ':' with
        | s::o::[] ->
            (match op_of_string o with
            | Some o -> Some (Cg.Pair (nat_of_string s, o))
            | _ -> None)
        | _ -> None
    ) with
    | _ -> None  

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

let string_of_op (o:Cg.op) =
    match o with
    | Cg.ASYNC _ -> "async"
    | Cg.ASYNC_PHASED _ -> "phased"
    | Cg.SIGNAL _ -> ""
    | Cg.WAIT _ -> ""
    | Cg.DROP _ -> ""
    | Cg.PREC -> "signal"
    | _ -> ""

let is_sync (o:Cg.op) =
    match o with
    | Cg.PREC -> true
    | Cg.ASYNC _ -> true
    | Cg.ASYNC_PHASED _ -> true
    | _ -> false


let string_of_edge e =
    match e with
    | Cg.Pair (o, Cg.Pair (v1, v2)) ->
        let n1 = (int_of_nat v1) in
        let n2 = (int_of_nat v2) in
        Printf.sprintf "%d -> %d %s" n1 n2 (string_of_op o);;

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

let string_of_graph es =
    concat "\n" (List.map string_of_edge (filter_duplicates (as_list es)))

let trace_of_string s =
    let to_evt x : Cg.event list = match (event_of_string x) with
        | Some x -> [x]
        | _ -> []
    in
    from_list (rev (flatten (List.map to_evt (split s '\n'))))

let js_array_from_list l =
    let arr = jsnew Js.array_empty () in
    List.iteri (fun idx v -> Js.array_set arr idx v) l;
    arr

type edge = (Cg.node, Cg.node) Cg.prod

type ex_edge = (Cg.op, edge) Cg.prod

let js_of_vertices (vs:Cg.tid Cg.list) =
    let to_js (idx:int) (tid:int) =
        Js.Unsafe.obj [|
        ("id", Js.Unsafe.inject idx);
        ("label", Js.Unsafe.inject idx);
        ("group", Js.Unsafe.inject tid)
        |]
    in
    let rec convert idx xs =
        match xs with
        | x::xs -> to_js idx (int_of_nat x) :: (convert (idx+1) xs)
        | [] -> []
    in
    js_array_from_list (convert 0 (rev (as_list vs)))

let js_of_edges (es:ex_edge Cg.list) =
    let to_js (e:ex_edge) =
        match e with
        | Cg.Pair (o, Cg.Pair(n1,n2)) ->

        Js.Unsafe.obj [|
        ("from", Js.Unsafe.inject (int_of_nat n1));
        ("to", Js.Unsafe.inject (int_of_nat n2));
        ("label", Js.Unsafe.inject (js (string_of_op o)));
        ("dashes", Js.Unsafe.inject (if is_sync o then Js._true else Js._false));
        ("arrows", Js.Unsafe.inject (js "to"));
        ("smooth", Js.Unsafe.js_expr (Printf.sprintf "{enabled: %s}" (if is_sync o then "true" else "false")))
        |]
    in
    js_array_from_list (List.map to_js (as_list es))

let js_of_cg cg =
    match cg with
    | Cg.Pair (vs, es) ->
    Js.Unsafe.obj [|
        ("nodes", Js.Unsafe.inject (js_of_vertices vs));
        ("edges", Js.Unsafe.inject (js_of_edges es)) |]

let draw_graph container g =
    let opts = Js.Unsafe.js_expr 
 "
{
  edges: {
    width: 2,
    smooth: {
        enabled: false,
    },
  },
  layout:{
    randomSeed: 0,
  },
  physics: {
    enabled: false,
  }
}"
    in
    Js.Unsafe.new_obj (Js.Unsafe.variable "vis.Network")
    [| Js.Unsafe.inject container;  Js.Unsafe.inject g; opts|];
    Js._false 

let parse_cg container t =
    match Cg.build t with
    | Cg.None -> Js._false
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
    let graph =
        Js.Opt.get (Html.document##getElementById(Js.string "graph_out"))
        (fun () -> assert false) in
    txt##onkeyup <- Html.handler (
        fun _ ->
        let trace_txt = Js.to_string (txt##value) in
        let t = trace_of_string trace_txt in
        parse_cg graph t
    );
    Js._false

let _ =
    Html.window##onload <- Html.handler onload

