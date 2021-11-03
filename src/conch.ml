open Libconch

let die fmt = Common.die ~where:"driver" fmt

let () =
  let input, output =
    match Sys.argv |> Array.to_list |> List.tl with
    | [input_file; output_file] -> input_file, output_file
    | _ -> Printf.eprintf "Usage: %s <input file> <output.rom>\n" Sys.argv.(0); exit 1
  in
  match CCSexp.parse_file_list input with
  | Error err -> die "Cannot parse input file: %s" err
  | Ok sexps ->
    let sexps = Frontend.preprocess_sexps sexps in
    let prog = Frontend.prog_of_sexps sexps in
    let cm_prog = Lang2cminor.translate_prog prog in
    Format.set_margin 30;
    List.iter (fun sexp ->
      Format.fprintf Format.std_formatter "%a\n@." CCSexp.pp sexp
    ) (Cminor.sexps_of_prog cm_prog);
    let asm = Codegen.program cm_prog in
    Format.fprintf Format.std_formatter "%a\n" (Target.pp_asm Codegen.prog_start) asm;
    let bytes = Target.assemble asm in
    CCIO.with_out output (fun out -> List.iter (output_byte out) bytes)
