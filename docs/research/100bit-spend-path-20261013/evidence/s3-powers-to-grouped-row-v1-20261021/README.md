# S3 powers to current low-array grouped-row composition

This focused theorem starts from two canonical current-carrier bases, obtains successful N=4 generated power-array model runs, maps their values through the proved current/power inverse carrier maps, and supplies those exact arrays to the P6 current low-array helper. It derives the helper input canonicality rather than assuming it, then composes the checked grouped source-row theorem.

The proof is green under Lean 4.32.0 with `-j1 -M 4400`, no option overrides, and standard axioms `[propext, Classical.choice, Quot.sound]`. The exact target source, launch preflight, command, log, resource report and receipt are retained in this directory. The compiled object is not included; its hash and external local-cache location are recorded.

This result remains a model/cut composition. Rust `core::array::from_fn` correspondence and reachability through the enclosing Rust `Weights::pair` branch remain open.
