<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# CwF-like structure of the de Bruijn encoding






Formalization of constructions on unityped weak categories with families and of presentations for the binding syntax of the lambda calculus

## Meta

- Author(s):
  - Matteo Calosci (initial)
- License: [MIT License](LICENSE)
- Compatible Rocq/Coq versions: 9.0
- Additional dependencies:
  - [Category Theory in Coq](https://github.com/jwiegley/category-theory)
  - [MathComp boot](https://math-comp.github.io/)
- Rocq/Coq namespace: `CwFdeBruijn`
- Related publication(s): none

## Building instruction:
Use [OPAM](https://opam.ocaml.org/doc/Install.html):
```shell
opam switch create rocq-env 5.4.0
eval $(opam env)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install . --deps-only
make
```


