Conch
=====

Compiler for a C-like language to [Uxn](https://wiki.xxiivv.com/site/uxn.html).

This is very much a work in progress.

Building
--------

Building requires `ocaml`, `dune` and the `containers` ocaml library.
The recommended way to install those is by using [opam](https://opam.ocaml.org).

Then:

```
make
_build/default/src/conch.exe input.cm output.rom
```

Input language
--------------

See the [examples/](examples) directory for some examples.
