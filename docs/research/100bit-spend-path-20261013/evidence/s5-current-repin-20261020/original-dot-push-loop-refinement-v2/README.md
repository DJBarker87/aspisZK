# Original emitted Dot.push loop refinement (v2)

This source-only packet ties the emitted nominal `fast_pairing.canonical.Dot.push` loop to the four-coordinate literal loop theorem. It retains the original extraction inputs/generated Funs and Types, the mechanically adapted source owner, the Lean proof source, source checker, and extraction/proof receipts. It intentionally omits compiled `.olean` files and the LLBC binary; the LLBC hash is recorded in `source/input/source-pins.json`.

The checker verifies the Types source modulo removal of generated `set_option` lines, and exact token-equivalence of generated `P`, `push_loop.body`, and `push_loop` definitions to the adapter. It verifies that the outer `Dot.push` body changes only by replacing the opaque `Q.raw a b` call with an explicit `rawFn a b` parameter. The Lean theorem then proves literal-four loop output and successful `push_raw` output. The proof imports no `FunsExternal` template.

Boundary: this is not a theorem that the external Rust `Q.raw` implementation equals the explicit callback, nor a full Rust standard-library refinement. The current caller identity and raw function semantics remain open. This packet does not claim the overall S5 current-repin goal is complete.

Accepted proof target: `OriginalDotPushRawLoopToLiteralV1`; source SHA `9b50e4e17a6ae41a556df0425d2bed9139f48ece54a6b37530afe73abdcee3cd`; object SHA `781c786019bcea212ea2a6cefc8b602e45b186faef5a5895d79dc011b519daa8`; exit 0, 2.308 s, RSS 2,396,168 KiB, cgroup peak 309,911,552 bytes, swap 0; axioms for the three exported theorems are `propext`, `Classical.choice`, and `Quot.sound`. Exact receipt and preflight are under `evidence/proof-v4/`.
