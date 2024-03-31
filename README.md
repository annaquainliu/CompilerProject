# CompilerProject
allegedly

Initialize compiler: eval "$(opam env)"

Compile: ocamlc str.cma -I +str -o interpret interpreter.ml
 ocamlfind ocamlc -package spectrum -linkpkg str.cma -I +str interpreter.ml

