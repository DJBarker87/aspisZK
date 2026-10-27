# Runjoin19 continuation of LOG D308

Target not yet established. Work remains in progress in the exact worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch `codex/pv-runjoin-20261026`, entry revision `fd42d798ff761071d79c3bd6fa4861190fd7e24a`. Budget 100 Lean, 0 Kani. No shipped code change, key operation, shared-source/object overwrite, push, or T-field addition.

## Endpoint authority audit

Ruling (h''') was applied recursively. Producer Funs/Types match the SHA-pinned freeze. Of 236 library objects at the exact selected paths, 218 hash-match and 18 have different hashes. The full closure also has 47 imports pinned by none of the three permitted authorities. These include `Init`, `Lean`, `Std.Do`, `Batteries.Data.BitVec.Lemmas`, and `Mathlib.Data.ZMod.Basic`; the complete names, paths, expected and actual hashes are in endpoint-resolution.json and library-hash-check.json. Under the explicit final sentence of (h'''), this step stops only: no substitute library object, private producer build, or endpoint axioms audit. No endpoint premise is removed by this audit.

## Proof progress

Indexed validator round-path connection proved: IndexedSbox19, IndexedFinalSbox19, IndexedRound00–21, IndexedCopy19.source. IndexedTarget19.round transports an existing model one-round equality to the actual source return by canonical-state injectivity. IndexedPair19.source composes two actual source rounds, including the leading external layer, checked division/index guards and both Option branches.

Concrete cell and bank proofs are being checked; only accepted receipts count. The source `CopyRecords.banks` constructor equation, actual selected-i compiler return, full transition, deployed PublicBinding and P∧hypotheticalT are not yet established. No successor is inferred from matching cells.

## Premise accounting

Recount **5**: **407 rows: 400 P, 3 T, 4 C; OPEN 93**. The 376 P / 26 T / 5 C counts were recount 3, not recount 5. V038, V045, V047, V152–V154 retained. Constructed P remains `{source public binding, trace}`; deployed P OPEN→OPEN; records 2/8/6→2/8/6. Endpoint premises removed/added/weakened 0/0/0. T remains exactly entropy_law, entropy_kernel, observation.
