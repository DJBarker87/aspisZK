# V184 reference/world counterexample

Branch `codex/pv-alib-20261027`, base and checked source revision
`aa27e73f99c51f8399d631e75a9bb517c3d03575`. Worktree remains
`/Users/dominic/ZK/.worktrees/pv-alib`. **Target not yet established.**

## Stop and exact scope

The proposed V184 P6 strengthening tested here was:

> For every admissible generic vector input, native `Vec.pop` and
> `pop_slices_reference`, with an initially empty output vector, agree in
> the returned value, remaining contents, and allocation/deallocation trace.

This strengthening is **false**. For `T=u8` and `[17,29]`, both return
`Some(29)` with remaining contents `[17]`. Native pop retains its original
buffer and capacity and performs zero allocations, reallocations and
deallocations. The exact existing safe copy reference performs one allocation.
The reference function body is copied verbatim from
`tools/pv-cblib-20261027/lib.rs`; `pop-reference-pin.json` records the body
and hashes. The test resets allocator counters immediately before each call
and snapshots them immediately after; formatting and assertions occur later.
Both test vectors and the native allocation are constructed before measurement.

`native-pop-world-pinned-02-output.log` confirms this on the source-corpus
toolchain, rustc **1.98.0-nightly (14210df0e, 2026-05-31)**,
`nightly-2026-06-01`, optimized. Its receipt is
`native-pop-world-pinned-02-receipt.json`: exit 0, wall 0.12 s,
116428 KiB peak RSS, swaps 0. The first check used host-default rustc 1.94.1;
it is retained as a separate measurement, not passed off as the pinned check.
The second run changes the toolchain explicitly, not the caps or statement.

This is a checked counterexample to the proposed **native-to-reference world
refinement for V184**, not a counterexample to `Vec.pop`'s value law, to the
accepted loop lemmas, or to the existence of another valid reference.
No already accepted callback theorem asserted this stronger world law.
Following the requested checked-counterexample stop, no repair, weakened
world projection, new premise, further row work, or budget-filling replay was
attempted. The budgets are unspent for this reason, not because of a host gate.

There is an independent non-vacuity obstruction in the prior plan
`tools/pv-cblib-20261027/resume9-std-plan.md`: it says `Word` is Copy.
The selected source at `host_commitment.rs:107` instead has
`Word::Base(Vec<M31>)` and `Word::Secure(Vec<QM31>)`, with no Copy
implementation. `encoded.pop()` at line 253 consumes
`Result<Word,Error>`. The native `T:Copy` reference cannot instantiate that
payload. The Lean marker-erasure fact does not establish a Rust Copy instance.
The `u8` counterexample above already satisfies the reference's actual Copy
bound; its failure does not rely on this separate obstruction.

## Row accounting

| Row | Before residual | After residual | Closing theorem | Status change |
|---|---|---|---|---|
| V184 / op33 | `ProverRwFull.ExternalFuns.op33` exact source/native callback, complete Result and world | Same; the tested copy-reference world refinement is refuted | None | OPEN -> OPEN |
| V233 / op209 | `ProverRwFull.ExternalFuns.op209` selected split-block callback for arbitrary sized slices and consumed-callback link | Same; stopped before implementation | None | OPEN -> OPEN |
| V265 / op259 | `ProverRwFull.ExternalFuns.op259` missing native/reference gate; prepared selector is insufficient | Same; stopped before implementation | None | OPEN -> OPEN |

The full recount-5 input rows are retained in `input-rows5.json`. No canonical
ledger or endpoint source is edited. No endpoint/deployment premise is removed,
added, weakened or transferred to T. V232 and the three-field trust list are
unchanged. No claim about SHA-NI semantics is made.

## Kernel-checked supporting work

Five new, small modules compile in the private objects directory:

* `PV_AL_PopUnfold.unfold_loop`: exact one-step unfolding of the existing
  extracted copy loop, using the existing generic loop equation.
* `PV_AL_PopStep.done` and `.continuing`: exact complete-Result body cases;
  the continuing branch retains the vector returned by push.
* `PV_AL_PopPrefix.length` and `.advance`: capacity bound and one-element
  copied-prefix invariant.
* `PV_AL_PopLoop.source`: every loop input with
  `last.val <= v.val.length`, `i.val <= last.val`, and
  `out.val = v.val.take i.val` returns `ok a` with
  `a.val = v.val.take last.val`, by decreasing remaining length.
* `PV_AL_PopLast.last` and `.dropLast`: general list identities.

The loop premises are satisfiable for every slice by `i=0`, empty `out`,
and any representable `last <= len`; they describe the loop's starting
prefix, not the eventual result. No native equality or world law is a premise
of these supporting theorems. They do not close V184 and are not advertised
as complete `pop_slices_reference`/selected-op33 source laws.

`POP-FIDELITY-SCAN.json` records the function-specific dropped-restoration
scan: no iterator/element mutable borrow or discarded backward continuation
in this emission. The updated output is explicitly carried as `out1`.
The native world differential above is retained, including its mismatch.
No D188 source credit is inferred from a static scan alone.

## Receipts, pins and budget

`RECEIPTS.json` contains every exact target, source SHA/revision, direct import
object hash, exit, wall time, peak RSS, swaps and full `#print axioms` output.
Focused attempts 52700–52703 and 52705 pass; 52704 failed on list notation and
an implicitly bound lemma argument, then changed source passed at 52705.
Its rejected snapshot and diagnostic `sorryAx` output are retained; no accepted
source contains a proof placeholder. Every accepted axiom set is a subset of
`{propext, Classical.choice, Quot.sound}`.

* Lean: **6/100** charged, **5 accepted / 1 rejected**.
* Kani: **0/6**. No chained-field-arithmetic Kani was attempted.
* Native Rust: two optimized differential checks, each separately receipted.
* Lean wall times 1.10–1.63 s; maximum accepted RSS 2631024 KiB; all swaps 0.
* One scope at a time; MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0,
  TasksMax 64; Lean -M7000; no local Lean.
* `ID-PREFLIGHT.json` records existing CBL consumption of 52500–52507 and
  52697–52699. They were excluded. Only 52700–52705 were used here.
  Audit IDs 52997–52999 remain unused and reserved.
* No shared env-J source writes. Existing objects are read through private
  links, with their effective direct-import hashes in each receipt.
* No `crates/` or `programs/` changes and no ELF rebuild. Release pins are
  inherited, **not freshly confirmed**: default
  `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`,
  devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`,
  Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.

Next deliverable, after lead review of this counterexample: a native-compatible
non-Copy move reference for V184 with explicit retained buffer/capacity and
world behavior, followed by its extraction/source law and selected callback
link. The copying reference cannot be credited with the tested world law.
