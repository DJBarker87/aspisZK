Private Aeneas decoder printer compatibility candidate, 2026-10-16

The b59 emitted decoder failed Lean4.32 parsing at Funs3241 and5286–5326.
Nested frontier control flow reaches OCaml Format's default max_indent68:
constructor, argument and branch body collapse to the same indentation.
The pinned Translate.ml:1421 sets margin80. Increasing margin alone preserves
the old maximum indent in the pinned OCaml5.2 Format implementation.

Private patch: replace that one statement with
Format.pp_set_geometry fmt ~max_indent:1000 ~margin:1024;
All776 original source files were checked against the original source archive;
only Translate.ml changes. A distinct version label records geometry1024.
The original tool and cache are untouched. No Rust or Lean body was rewritten.

Incremental optimized native tool build: exit0,6.311s,522404KiB peak RSS,
738766848bytes cgroup peak,zero swap. The actual Docker scope had6GiB high,
8GiB max,swap0 before the compiler was released. Its image is pinned, network
disabled,root filesystem read-only, and the original Charon library mounted
read-only. This reused an independent copy of the original Aeneas build cache.

New binary SHA256:
849dc33c427441499c7364d3d7c6426e2ef48be7f9859ab8456efc859394ebd0.
Regeneration uses the same72a288c2c Rust source and same renamed LLBC:
exit0,21.396s,3930080KiB RSS,4014178304bytes cgroup peak,zero swap,6/8/0.
The binary,original source archive,patch,all source pins,raw build logs and
regenerated files are retained. verify.py checks this provenance only.
Separate token comparison, focused compilation and actual axiom checks are
required; no decoder correctness or closed-extraction claim is made here.
