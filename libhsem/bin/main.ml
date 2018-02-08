
let () =
    if Array.length Sys.argv == 2 then(
        Hsem.parse (Sys.argv.(1));
(*        Sys.argv.(1) |> print_string;
        print_string "\n";*)
        ()
    )else
        print_string "Usage: hsem <FILENAME>\n";
        exit 0;;
