# Literal semantic view evidence

This bundle records the focused compile of `R1LiteralSemanticView` and its direct import sources/objects. The theorem gives a fixed-prefix, table-free bound for the semantic challenge under the selected literal-message view. It does not establish full D2/D3 or Fiat–Shamir closure, terminal acceptance, Rust source refinement, or a complete extractor.

Attempt `b` passed in 2.68 s at 3,605,968 KiB peak RSS with zero swap under the recorded 4G/6G/0 cgroup. Its two public axiom reports use `propext`, `Classical.choice`, and `Quot.sound`. Failed attempt `a` is preserved; it emitted two reports, one containing `sorryAx`, and is not accepted as a successful proof.

Direct import source and object hashes are recorded in `source-manifest.json`. `R0P.MaskD2Glue` is an existing cached dependency from the `aspis-fs-generic-20261006` workspace: the R1 object resolves to that cache and its source pin is retained from the v8 source tree. No new compilation of that old module is claimed here.
