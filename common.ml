let die ~where fmt =
  Format.kasprintf (fun s -> Format.fprintf Format.err_formatter "ERR (%s): %s\n" where s; exit 1) fmt
