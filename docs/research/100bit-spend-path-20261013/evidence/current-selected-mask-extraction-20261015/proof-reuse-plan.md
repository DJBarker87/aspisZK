# Selected-mask extraction / arithmetic proof reuse plan

Inspection is read-only. Attempt-b produced Aeneas Lean source at `/tmp/aspis-r1-mask-extraction-20261015/attempt-b/output/generated/AspisR1SelectedMaskProbe/`.

## Generated source comparison

SHA-256: selected-mask `Types.lean` `67e0b79e68da4390cc1d350da23cd6ea90daf13bf2ab58cf9e59ef2bd91270d2`, `Funs.lean` `a9798fcd2e62b3443745dbc2ae9e2694cd18975e8f509ffe54d7e2c38402661a`; current arithmetic-probe proof-source files are `Types.lean` `c5a08408bb25ca84fcef1b3689904d27e65510c21775d6db8beeb271fbaa5b15`, `Funs.lean` `114552b863f61e970a2ceb4bb048566e4b464b61905c6d7a175f6b117f1aed4a`.

After replacing only the generated module root `AspisR1SelectedMaskProbe` with `AspisR1Qm31ArithmeticProbe` and ignoring Aeneas crate-name doc comments:

- The common `field.M31`, `field.CM31`, `field.QM31` type declaration bodies match exactly. Both have `M31 := Std.U32`, the same `CM31 {a,b}` and `QM31 {c0,c1}` layouts. These are still distinct Lean constants because they live in different namespaces.
- Thirteen common declarations match exactly: twelve function bodies plus the global `field.P` definition: `field.P`, `field.reduce_u64`, `field.M31.add/sub/mul/reduce_u64/double`, `field.CM31.add/sub/mul`, `field.QM31.add/mul`, and `field.mul_by_r`.
- Selected-mask output adds the `PreparedQm31Multiplier` type/closures and additional field/state-only helpers. Current arithmetic output has its separate `qm31_add_mul_probe` entrypoint. This difference is expected from the extraction roots; it does not change the common declarations.

The comparison was textual on generated declaration bodies, not a Lean theorem equating the two namespaces or a Rust refinement result.

## Import/rename plan

Exact aliases are insufficient: generated selected-mask functions are typed over `AspisR1SelectedMaskProbe.field.*`, while existing arithmetic proofs quantify over `AspisR1Qm31ArithmeticProbe.field.*`. Even structurally identical record declarations in distinct namespaces are different Lean types, and the generated operation constants are correspondingly distinct.

Reuse the proof route by producing a retargeted proof chain that imports `AspisR1SelectedMaskProbe.Funs` and changes the generated namespace references from `AspisR1Qm31ArithmeticProbe` to `AspisR1SelectedMaskProbe`. The existing chain and source hashes are:

| Existing proof module | Import predecessor | SHA-256 |
|---|---|---|
| `ExtractedCurrentReducerOps.lean` | current arithmetic `Funs` | `393671317c3199ed4d62f1b6ec65e848ec9c831d0dfad740ea0f5ceed47595a5` |
| `ExtractedCurrentReducer.lean` | reducer ops | `933ae275dac978bd0ac60035154e5274c4f1a12bffcbc98f2265fbd50e49af74` |
| `ExtractedCurrentM31AddSub.lean` | current arithmetic `Funs` | `84100aa24d1e1431798195ff0d5d548ac6e03cd3c0149c5a3251833f30bec568` |
| `ExtractedCurrentTowerAdd.lean` | M31 add/sub | `99af475da13f6066d8aefbbf19c062858648abea980a94e98bc1ed14488e5166` |
| `ExtractedCurrentCM31Mul.lean` | reducer + tower add | `0364f578089cdf613c406f527d59096673c84242f5cabfc2c13c6ed05075ab1d` |
| `ExtractedCurrentQM31Mul.lean` | CM31 mul + tower add | `954b173f71eaf1c59da6ff32e9fbe10a9047fbcca622b85a85a01588b0134d66` |
| `ExtractedCurrentQM31Tower.lean` | QM31 mul + pure historical word tower | `c350218ee48adef372f56b6f108a916dccacff6057c548b462b0f824a883e881` |
| `ExtractedCurrentQM31Exact.lean` | QM31 tower + `ExactTowerBase` | `8ebed6587ee751e9296218f2618185d4c49de533a094232c62c551705add0e34` |

This is a separate focused Lean compilation chain, not an alias-only cache hit. Historical pure word-tower/ExactTowerBase imports remain reusable as-is because they do not depend on the generated arithmetic carrier. The current `ExtractedCurrentQM31Equality` theorem likewise cannot directly prove injectivity for the new selected-mask carrier; it needs a namespace-retargeted instance of the same coordinate argument. No parser or source semantics claim follows from this import plan.
