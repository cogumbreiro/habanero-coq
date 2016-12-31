module Html = Dom_html

open List
open Printf
open String
open Stringext

type node_type =
    | Past of Cg.op
    | Current of Cg.taskview

type edge_type =
| FORK
| SYNC
| CONTINUE


module IntHash =
    struct
        type t = int
        let equal i j = i=j
        let hash i = i land max_int
    end

module I = Hashtbl.Make(IntHash)

let js = Js.string
let js_array a =
    let arr = jsnew Js.array_empty () in
    Array.iteri (fun idx v -> Js.array_set arr idx v) a;
    arr

let _REG = "reg"
let _SO = "SO"
let _WO = "WO"
let _SW = "SW"

let reg_of_string s : Cg.regmode =
    let s = trim s in
    if s = _WO then Cg.WAIT_ONLY
    else if s = _SO then Cg.SIGNAL_ONLY
    else if s = _SW then Cg.SIGNAL_WAIT
    else raise (Failure "reg_of_string")

let string_of_reg r =
    match r with
    | Cg.SIGNAL_ONLY -> _SO
    | Cg.SIGNAL_WAIT -> _SW
    | Cg.WAIT_ONLY -> _WO

let op_of_string s =
    match split (trim s) ' ' with
    | "reg" :: x :: r :: [] -> Cg.REGISTER { Cg.get_task = int_of_string x; Cg.get_mode = reg_of_string r }
    | "signal" :: [] -> Cg.SIGNAL
    | "wait" :: [] -> Cg.WAIT
    | "drop" :: [] -> Cg.DROP
    | _ -> raise (Failure "op_of_string")

let event_of_string s : Cg.event =
    let s = trim s in
    match split s ':' with
    | s::o::[] -> (int_of_string s, op_of_string o)
    | _ -> raise (Failure "op_of_string")

let registry_to_js_aux (r:Cg.registry) =
    [
        ("dst", Cg.get_task r |> Js.Unsafe.inject);
        ("mode", Cg.get_mode r |> string_of_reg |> js |> Js.Unsafe.inject)
    ]

let registry_to_js (r:Cg.registry) : 'a Js.t =
    r |> registry_to_js_aux |> Array.of_list |> Js.Unsafe.obj

let js_to_registry j: Cg.registry =
    {
        Cg.get_task = (Js.Unsafe.coerce j)##dst;
        Cg.get_mode = (Js.Unsafe.coerce j)##mode |> Js.to_string |> reg_of_string;
    }

let string_of_op o =
    match o with
    | Cg.REGISTER r -> "reg " ^ (string_of_int (Cg.get_task r)) ^ " " ^ (string_of_reg (Cg.get_mode r))
    | Cg.SIGNAL -> "signal"
    | Cg.WAIT -> "wait"
    | Cg.DROP -> "drop"

let op_name o =
    match o with
    | Cg.REGISTER _ -> "reg"
    | Cg.SIGNAL -> "signal"
    | Cg.WAIT -> "wait"
    | Cg.DROP -> "drop"

let op_to_js (o:Cg.op) =
    let l = ("name", o |> op_name |> js |> Js.Unsafe.inject) :: match o with
        | Cg.REGISTER r -> r |> registry_to_js_aux
        | _ -> []
    in
    l |> Array.of_list |> Js.Unsafe.obj

let js_to_op j =
    match trim ((Js.Unsafe.coerce j)##name |> Js.to_string) with
    | "reg" -> Cg.REGISTER (js_to_registry j)
    | "signal" -> Cg.SIGNAL
    | "wait" -> Cg.WAIT
    | "drop"-> Cg.DROP
    | _ -> raise (Failure "js_to_op")

let event_to_js ((t,o):Cg.event) : 'a Js.t =
    js_array [| t |> Js.Unsafe.inject; o |> op_to_js |> Js.Unsafe.inject |]

let js_to_event (j:'a Js.t) : Cg.event =
    match Js.to_array (Js.Unsafe.coerce j)  with
    | [| t; o |] -> (Js.Unsafe.coerce t |> Js.parseInt, js_to_op o)
    | _ -> raise (Failure "js_to_event")

let trace_to_js (t:Cg.event list) =
    List.map event_to_js t |> Array.of_list |> js_array

let js_to_trace j =
    Js.to_array j |> Array.to_list |> List.map js_to_event

let taskview_to_js (v:Cg.taskview) =
    Js.Unsafe.obj [|
        ("wp", Cg.wait_phase v |> Js.Unsafe.inject);
        ("sp", Cg.signal_phase v |> Js.Unsafe.inject);
        ("mode", Cg.mode v |> string_of_reg |> js |> Js.Unsafe.inject)
    |]

let js_to_taskview j : Cg.taskview =
    {
        Cg.wait_phase = (Js.Unsafe.coerce j)##wp;
        Cg.signal_phase = (Js.Unsafe.coerce j)##sp;
        Cg.mode = (Js.Unsafe.coerce j)##mode |> Js.to_string |> reg_of_string;
    }

let phaser_to_js (ph:Cg.phaser) =
    let handle (k,v) = (string_of_int k, v |> taskview_to_js |> Js.Unsafe.inject) in
    ph |> Cg.Map_TID.elements |> List.map handle |> Array.of_list |> Js.Unsafe.obj

let js_to_phaser j : Cg.phaser =
    let handle (ph:Cg.phaser) (k:Js.js_string Js.t) =
        Cg.Map_TID.add (Js.to_string k |> int_of_string) (Js.Unsafe.get j k |> js_to_taskview) ph
    in
    List.fold_left handle Cg.Map_TID.empty (Js.object_keys j |> Js.to_array |> Array.to_list)

let string_of_taskview v =
    ("sp: " ^ string_of_int (Cg.signal_phase v) ^
    "\nwp: " ^ string_of_int (Cg.wait_phase v) ^
    "\nmode: " ^ string_of_reg (Cg.mode v))

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



let js_of_node_type (n:int) (nt:node_type option) sp wp =
    let phase_of sp label n : string =
        match Cg.MN.find n sp with
        | Some ph -> Printf.sprintf "\n%s: %d" label ph
        | _ -> ""
    in
    let handle_op o : string =
        let o_sp = phase_of sp "sp" n in
        let o_wp = phase_of wp "wp" n in
        (string_of_op o) ^ o_sp ^ o_wp
    in
    js (
        match nt with
        | Some (Past o) -> handle_op o 
        | Some (Current v) -> "\n\n" ^ string_of_taskview v
        | _ -> ""
    )

let js_of_vertices (vs:int array) b (ph:Cg.phaser option) =
    let ns = Cg.node_to_op b in
    let sp = snd (Cg.get_sp b) in
    let wp = snd (Cg.get_wp b) in
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
        ("label", Js.Unsafe.inject (js_of_node_type idx nt sp wp));
        ("group", Js.Unsafe.inject tid);
        ("font", Js.Unsafe.inject font)
        |]
    in
    Array.mapi to_js vs

let js_of_bool b = if b then Js._true else Js._false

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

(** Build a graph from a given trace *)
let js_of_cg (b,cg) (ph:Cg.phaser option) =
    let tids = Array.of_list (rev (Cg.get_nodes b)) in
    Js.Unsafe.obj [|
        ("nodes", js_of_vertices tids b ph |> js_array |> Js.Unsafe.inject);
        ("edges", js_of_edges cg |> js_array |> Js.Unsafe.inject)
    |]

let _ =
    let run_trace = Js.wrap_callback (fun t -> 
        match t |> js_to_trace |> Cg.reduces_trace with
        | Some ph -> phaser_to_js ph
        | _ -> raise (Failure "Invalid trace!")
    ) in
    let build_cg = Js.wrap_callback (fun t ->
        let t = js_to_trace t in
        match Cg.build t with
        | Some g -> js_of_cg g (Cg.reduces_trace t)
        | _ -> raise (Failure "Invalid trace!")
    ) in
    let run = Js.wrap_callback (fun e ph ->
        match Cg.reduces_dec (js_to_event e) (js_to_phaser ph) with
        | Cg.Inl ph -> phaser_to_js ph
        | _ -> raise (Failure "Cannot reduce!")
    ) in
    let hb = Js.wrap_callback (fun x y ->
        Cg.hb_dec (js_to_phaser x) (js_to_phaser y) |> js_of_bool
    ) in
    let par = Js.wrap_callback (fun x y ->
        Cg.par_dec (js_to_phaser x) (js_to_phaser y) |> js_of_bool
    ) in
    let wf = Js.wrap_callback (fun x ->
        Cg.Phaser.well_formed_dec (js_to_phaser x) |> js_of_bool
    ) in
    let wo = Js.wrap_callback (fun x ->
        Cg.well_ordered_dec (js_to_phaser x) |> js_of_bool
    ) in
    Js.Unsafe.global##hj <-
    Js.Unsafe.obj [|
        ("run_trace", Js.Unsafe.inject run_trace);
        ("graph", Js.Unsafe.inject build_cg);
        ("run", Js.Unsafe.inject run);
        ("hb", Js.Unsafe.inject hb);
        ("par", Js.Unsafe.inject par);
        ("wf", Js.Unsafe.inject wf);
        ("wo", Js.Unsafe.inject wo);
    |]
    (*|> Js.export_all*)

