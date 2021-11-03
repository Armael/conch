open Libconch

let die fmt = Common.die ~where:"test" fmt

let compile (file: string): Cminor.program * Target.inst list * string =
  let sexps =
    match CCSexp.parse_file_list file with
    | Error err -> die "Cannot parse input file: %s" err
    | Ok sexps -> sexps
  in
  let sexps = Frontend.preprocess_sexps sexps in
  let prog = Frontend.prog_of_sexps sexps in
  let cm_prog = Lang2cminor.translate_prog prog in
  let asm = Codegen.program cm_prog in
  let bytes_l = Target.assemble asm in
  let rom = String.of_seq (List.to_seq bytes_l |> Seq.map Char.chr) in
  cm_prog, asm, rom

let run (rom_file: string): string =
  let cin = Unix.open_process_in (Filename.quote_command "uxncli" [rom_file]) in
  let stdout = CCIO.read_all cin in
  let _ = Unix.close_process_in cin in
  stdout

let output_dir = "test/expect"

let test (file: string) =
  Printf.eprintf "Testing %s... " file;
  let basename = Filename.basename file |> Filename.chop_extension in
  let cm, asm, rom = compile file in
  (try Unix.mkdir output_dir 0o755 with
     Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  let stdout =
    let romfile = Filename.temp_file "conch_test_rom" basename in
    CCIO.with_out romfile (fun cout -> output_string cout rom);
    run romfile
  in
  let write_outputs =
    List.iter (fun (name, out) ->
      CCIO.with_out (Filename.concat output_dir (basename ^ "." ^ name))
        (fun cout -> output_string cout out)
    )
  in
  let cm_str =
    let b = Buffer.create 80 in
    let fmt = Format.formatter_of_buffer b in
    Format.set_margin 30;
    List.iter (fun sexp ->
      Format.fprintf fmt "%a\n@." CCSexp.pp sexp
    ) (Cminor.sexps_of_prog cm);
    Buffer.contents b
  in
  let asm_str =
    let b = Buffer.create 80 in
    let fmt = Format.formatter_of_buffer b in
    Format.fprintf fmt "%a\n" (Target.pp_asm Codegen.prog_start) asm;
    Buffer.contents b
  in
  let rom_str =
    Printf.sprintf "%d bytes" (String.length rom)
  in
  Printf.eprintf "%s\n" rom_str;
  write_outputs [
    "cminor", cm_str;
    "asm", asm_str;
    "romsize", rom_str;
    "out", stdout;
  ]

(********************)

let () =
  List.iter test [
    "examples/array.cm";
    "examples/fibo.cm";
    "examples/hello.cm";
    "examples/if.cm";
    "examples/list.cm";
    "examples/loop.cm";
    "examples/printint.cm";
    "examples/tuto_day2.cm"
  ]
