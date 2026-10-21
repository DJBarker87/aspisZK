# S4 head forward execution continuation

Target remains `OraclePortHeadlineFrozen2PerAttempt.final_soundness` and `AcceptedRunJoin` for `dV_frozen2`. These are focused source-model arithmetic results, not closure of S4 or of the implementation-linked headline.

Proved and committed on research:

- `17e1ac864`: actual head limb multiply/add/update forward execution, then phase-sensitive output bounds.
- `af1d4b03b`: generated eight-limb head loop forward execution via symbolic induction on remaining limbs. Canonical coefficient/scalar and incoming uniform/suffix bounds imply source loop success and the outgoing `(k+1)*cap` bound.
- `ae82b444f`: actual query-values caller success links to generated four-dots success and all four callback traces on the same mapped coefficient array and exact 608-byte query prefix.
- `c55b7c52c`: actual checked offsets, slice, four-byte array conversion, and coefficient read from slot<4 and term<26; full per-term assembly derives inner-loop success from bounds.
- `5e1203117`: carry each callback's existing exact source-field functional result through the caller join without dependent elimination of its large payload.
- `7e3e8e6cb`: install the retained strict M31 parser, exact wide-to-limbs operation and eight-limb constant into the actual per-term body. Derive scalar and coefficient bounds and conversion/inner-loop success. Remaining inputs: exact parser acceptance, canonical selected Wide coefficient, and incoming k-cap bound.

Each root packet records compiler/source/object hashes, launch revision, command, focused exit status, wall time, peak RSS, swap and standard-axiom reports. No production Rust source changed. No full manifest replay or CU gate was repeated.

## Further proved execution composition

- `7d8eda38f`: full bounded per-batch term loop, deriving each selected coefficient's canonicality from the original array.
- `9d474e32c`: actual partial-fold limb body and complete eight-limb loop. This uses a deliberately coarse execution envelope to construct every checked call; tighter retained per-coordinate semantic bounds remain separate.
- `e746e660e`: complete actual outer batch body, including checked range selection and both inner loops.
- `0e3508549`: full actual outer head loop, deriving the StepBy calls and using induction on the remaining batch count.
- `822586212`: initialized seven batches from the actual zero limb array and source iterator initialization. Exact strict parser acceptances for 26 head records and canonicality of the 29 coefficient inputs remain premises. Every head arithmetic and loop success is derived. The coarse final bound is `56 * (2^34 - 1)`, safely within U64.

Adjacent integration: `88ecb5afb` adds concrete EbyK new/first-push/finish product semantics; `766e0ffec` installs the genuinely extracted current wide-QM multiplication into scalar-factor operations; `02af43782` adds ClaimPowers carrier transport and a typed tx2 powers-to-query-loop same-array cut. These do not close their explicit source/Std/caller boundaries.

## Next head work and principal source blocker

1. Construct the N8 output reduction/packing call from the completed head limbs; reuse the existing canonical reducer and from-limbs proofs. Compose with committed full tail execution (`7505e9ce1`) and final current wide addition.
2. Derive strict parser acceptances from the actual caller's admissible proof bytes, and connect its coefficient origin to the ClaimPowers array. The same-array carrier transport and tx2 cut are now checked, but whole caller operation identity remains open.
3. **Shared P6/Std source correspondence remains a real blocker.** The actual Rust `array::from_fn` goes through `try_from_fn` and `try_from_fn_erased` over a mutable MaybeUninit buffer. Retained extraction attempts leave `try_from_fn` external or fail at `push_unchecked`; callback scheduling proofs for `from_fn_model` do not prove this buffer implementation. Worker Q is testing a candidate-only initialized-Copy-array bounded-while replacement for the smallest affected powers helper, with production and frozen sources untouched. No adoption, source equivalence, CU result, or frozen-endpoint proof is claimed for that candidate.
4. Full accepted-run/source/runtime and final frozen artifact joins remain required. Do not call S4 or the 100-bit implementation theorem closed from these focused execution results.

## Cache and focused runner locations

Root sources/objects and exact evidence are under `/tmp/root-s4-head-limb-forward-v3-20261021`, `/tmp/root-s4-head-loop-forward-v3-20261021`, `/tmp/root-s4-head-read-forward-v2-20261021`, `/tmp/root-s4-head-term-forward-v1-20261021`, and `/tmp/root-s4-current-head-term-forward-v1-20261021`. Packet sources/receipts are committed under `evidence/s4-*-forward-root-v1-20261021/`.

Prepend the retained Formatter repair closure before other Aeneas cache owners; reject any audit containing `core.fmt.Formatter`. This repair is a retained P6 model, not a proof of Rust Std correspondence. Use exact Lean 4.32, `-j1 -M4400`, owned mkdir lock and a live-process admission check; preserve unrelated live worktree edits.

Latest root warm objects: `/tmp/root-s4-head-batch-terms-forward-v2-20261021`, `/tmp/root-s4-limb-fold-forward-v5-20261021`, `/tmp/root-s4-limb-loop-forward-v2-20261021`, `/tmp/root-s4-head-batch-body-forward-v3-20261021`, `/tmp/root-s4-head-outer-forward-v3-20261021`, `/tmp/root-s4-seven-batches-forward-v1-20261021`, each under `objects/` with matching `sources/` and `evidence/`. No binary is committed.
