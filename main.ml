let die fmt =
  Printf.kprintf (fun s -> Printf.eprintf "ERR: %s\n" s; exit 1) fmt

let () =
  let input, output =
    match Sys.argv |> Array.to_list |> List.tl with
    | [input_file; output_file] -> input_file, output_file
    | _ -> Printf.eprintf "Usage: %s <input file> <output.rom>\n" Sys.argv.(0); exit 1
  in
  match CCSexp.parse_file_list input with
  | Error err -> die "Cannot parse input file: %s" err
  | Ok sexps ->
    let prog = Frontend.prog_of_sexps sexps in
    let cm_prog = Lang2cminor.translate_prog prog in
    let asm = Codegen.program cm_prog in
    Format.fprintf Format.std_formatter "%a\n" (Target.pp_asm Codegen.prog_start) asm;
    let bytes = Target.assemble asm in
    let out = open_out output in
    List.iter (output_byte out) bytes;
    close_out out
