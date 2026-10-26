# Per-step continuation (fresh allocation)

Branch `codex/cx-prover-rw-20261023`, base `5d97a425c5`.
Allocation: 100 Lean attempts, 20 Kani runs; Env-J 23700–23999.
Read shared pv-common rulings (a)–(d), r1p-common, local-lean and root
security/proof discipline. No production or existing proved module edits.

V164 before: owned compression/list equation proved, shipped correspondence open.
V163 before: whole proof/audit `data … = model` remains an explicit antecedent.
Callback remainder inherited: 31. No ledger row or endpoint premise removed yet.
Target not yet established.

## Source and sibling checks

At start pv-cb head is `55975ee0c6a68efbaab37317eca3209dbb03509d`.
Its worklist includes op223, op250 and all source callbacks in V169–V267
except the separately installed/assigned entries. Read-only use only; check
its current head again before any callback installation.

`generate.py` takes the literal shipped compression function and its exact loop
body from `crates/aspis-statement/src/logup.rs`. Generated wrappers expose the
post-state without modifying arithmetic. An indexed owned arity-16 reference
retains the final power update. `--check` requires exact generated text.
This is a checked textual association, not yet native whole-loop correspondence
or a kernel theorem about Rust machine execution.

## Split table

| Harness | Bound | Result |
| --- | --- | --- |
| `compression_state_step` | 2 | timeout240s, exit124; no certificate |
| `compression_accumulator_c0a` | 2 | timeout240s, exit124; split scale/add |
| `primitive_split::scale_c0a` | 2 | timeout240s, exit124; CaDiCaL, no reach checks |
| `primitive_split::add_c0a` | 2 | PASS0.37s |
| `compression_iterator16_next` | 18 | PASS11.79s |
| `scalar_mul_wrapper` | 2 | running, arithmetic refinement |

Expected time: optimized compilation, then one arbitrary-state native step,
with no stubs. Limits 6G/8G/swap0/Tasks64; 240-second timeout. Full arithmetic
and all eight output coordinates remain present. A timeout requires a smaller
successor, never a larger cap or an unchanged rerun.

## Lean23700

`PV_RW_CompressStep` passes: exit0,2.93s,4304028KiB RSS,zero swaps;
five standard-axiom reports. Exact modeled source-step sequence agrees with
owned step and its arbitrary-length Result iteration equals the retained fold.
No native machine/source association is inferred; V164 and V163 remain open.
Receipt and dependency manifest are committed alongside the exact input.

## Lean23701

`PV_RW_CompressBound` passes: exit0,2.44s,4306600KiB RSS,zero swaps;
four standard-axiom reports. Proves sufficient fuel = input length+1 for
arbitrary Result steps, specializes to17 for arity16, and proves the prefix
iterator bound. This does not cover compiler-generated memory-copy loops;
the native harness also keeps all unwinding assertions enabled.

Usage at this checkpoint:2/100 Lean,3/20 Kani launched. No row removed.

Native003 isolates the scale projection from the timed-out composed accumulator
and switches to Kani's documented built-in CaDiCaL. Still times out240s,
exit124,zero swap. No primitive certificate is inferred. Further split must
isolate multiplication/reduction, not repeat any of these harnesses unchanged.

## Lean23702 and literal extraction

`PV_RW_CompressReference` passes: exit0,2.70s,4312292KiB RSS,zero swap;
two standard-axiom reports. Exact step-source model = previously extracted
owned compression, all slices; bounded model with17 fuel = owned compression
on every typed16-cell array. No live callback installed.

The new literal compression step extracts and translates successfully with
unchanged pinned Charon/Aeneas. Both have independent receipts. A generated
new Lean module copies the exact emitted step body and adds source association
proofs. This is stronger source evidence, not a native full-loop certificate.

Native-input source audit compares234 production files in core/statement/cost
probe with the host preflight hashes: all match this base. The historical host
revision label is retained and explicitly distinguished from the branch pin.
This is not an artifact/release association. The full task scope still requires
actual source/native/effect adequacy, full proof/audit model equality and the
privacy endpoint/deployment conditions; none is silently dropped.

## Emission association and sampler steps

23703/PV_RW_CompressEmission passes2.22s/4311868KiB/zero swaps/two standard
axioms reports: literal emitted source step = modeled step, and fold equation.
The invocation revision-label typo is corrected explicitly in23703-revision-
correction.json; immutable source/dependency hashes and snapshots are unchanged.
23704/PV_RW_SamplerLimbBounds passes0.59s/763304KiB/zero swaps/five standard
reports: remainder<P and word<2^32 imply dividend<2^63<2^64; mathematical
remainder preservation and reverse-iterator prefix bound10.

Actual-M31 suffix-next007 passes2.78s; initial lifting008 passes0.30s;
reduce64 wrapper009 passes0.31s. Single sampler limb010 passes28.57s with
remainder<P, all raw words. Reverse iterator011 passes0.60s for every prefix
0..8. No stubs; all include unwinding assertions. Charon and Aeneas both
successfully process the literal sampler limb (separate receipts).

The raw external template for compression is archived as uncompiled text;
its emitted axiom placeholders are never imported. The accepted source module
uses the pre-existing parameterized primitive meanings instead. All accepted
kernel theorem audits contain only standard axioms. No new trusted axiom.

Native012 isolates just u32→u64 cast/product equality (no reducer/field carrier),
adds standard MIR optimization4, and passes13.55s. Native013 tests the smaller
literal scalar multiply/reducer factoring with that environment and times out
240s; no scalar correspondence claim. Native014 changes the compression
reference argument to a matched borrowed-value interface and exact statement
factoring, adds inline attributes, and checks the complete step with unchanged
resource/time limits. Earlier sources and rejected runs are retained.

23705/PV_RW_SamplerLimbSource passes2.48s/4304148KiB/zero swap,one standard
axiom report. Literal emitted source (with the retained shift32 API adaptation)
= owned machine operation sequence for all U32/U64 inputs, preserving Results.
No remainder bound is needed for this equation; bounds are separately proved.

Read-only pv-cb head recheck at15:41UTC:3c7d1a083101e71a000a71cb0ae0e10a0a1e113a.
No callbacks assigned there have been edited or installed here.

## Iterator source-model induction

23706 rejects one bind-normalization join in the cons theorem; exact rejected
source/log retained. No theorem from it is accepted (its error-generated
sorryAx reports are rejected).23707 destructures the returned pair explicitly
and passes1.97s/4316924KiB/zero swaps,all five reports standard. This proves
Aeneas.loop on the chosen remaining-list iterator model equals the extracted
owned compression for all inputs, including typed arity16. It does not claim
that failed Kani014 establishes the native step. No live op223 installation.

Native014 (matched borrowed interface/full step) times out240s. Its successor
015 is a single accumulator coordinate (a strict output/dependency split).
No caps/timeouts raised. V164 native full-step equality remains unsupplied.

## Sampler invariant, pass and array step

23708/PV_RW_SamplerLimbTotal passes1.92s/4297144KiB/zero swap/three standard
reports. The machine source leaf is total for every U32/U64 input; its next
remainder is strictly below P. No quotient/canonicality/output hypothesis.

Native016 passes52.11s: actual reverse-iterator array update equals owned full
array-state step for arbitrary eight raw words,1≤j≤8,remainder<P. Every updated
and untouched array slot, next remainder and index is checked; unwind10, no
stubs. Charon/Aeneas separately succeed for this complete array step.
23710/PV_RW_SamplerArraySource passes1.96s/4305780KiB/zero swap/three standard
reports: literal emitted array step+iterator control body equals retained
indexed body, hence the complete Result loop/pass equals retained reference.

23709 rejects pair-let rewriting;23711 rejects no-progress dsimp. Both exact
failed inputs retained and not accepted.23712 uses explicit congruence under
the remaining monadic continuation and passes1.79s/4305200KiB/zero swap/four
standard reports. Complete reverse-list pass source=owned plus per-step
remainder invariant/totality and output-length preservation are proved.
No op250/callback installation is claimed from these auxiliary source models.

## Final native allocation and bounded-source continuation

All20/20 Kani invocations are now used:12 passes,8 timeouts,zero counterexamples.
Native017 (power coordinate) times out240s. Native018 one-byte-word parser cell
passes1.27s;019 complete eight-word parser passes1.40s;020 literal decoder vs
retained owned decoder passes0.51s,all raw inputs. The latter three use bound34
to cover32-byte ABI/input copies; all unwinding assertions remain enabled.
No complete ordinary/compression native certificate is inferred merely by
counting component gates. Native Kani exhaustion is not a Lean stop.

23713 rejects a scalar numeral-bound normalization;23714 makes the Nat1 bound
explicit and passes1.99s/4298000KiB/zero swaps,four standard reports. It links
the complete new array loop to the proved old indexed machine source, and
transports actual step index-decrement/remainder invariants and totality.
23715 passes1.88s/4307828KiB/zero swap,four standard reports: the actual array
loop model equals finite(j+1),specializes to9 evaluations at arity8,and proves
that the native bound10 exceeds the user-loop evaluation count.

Read-only sibling check before source-model compression dictionary work:
pv-cb head3a16c923fddca9f2d48004fdff6318587ea237e1. Its final status marks op223
OPEN and op250 as a skipped earlier source-policy installation,with native
correspondence retained. No sibling-installed callback is edited or replaced.
The new compression dictionaries are auxiliary; no live callback installed.

## Closed compression and complete caller/data transport

23716/23717 reject record-update congruence inference;23718 instead rewrites the
explicit function equality and passes1.95s/4316324KiB/zero swap/standard axioms.
23720 complete auxiliary caller and BodyData transport passes1.74s/4309032KiB.
The whole proof/audit data equation is still an explicit antecedent,not supplied.

23719's closed arithmetic facts check,but binding through the full dictionary
hits the default200000-heartbeat whnf limit. This failed module is not accepted.
The replacement splits closed arithmetic(23722,1.76s/4316896KiB),selectors
(23721,1.75s/4304788KiB),and symbolic binding(23723,1.77s/4308916KiB). All pass
with standard axioms and zero swap; no limits raised. The emitted current step
is now proved equal to closed current field operations,total for every raw
input,and independent of every remaining ExternalFuns callback.

23724 rejects missing import/unused class inference;23725 rejects a redundant
tactic after simplification solved the goal;23726 passes1.79s/4315068KiB,
proving the complete closed arithmetic fold and its source-loop equation.
23727 rejects opaque-zero rfl;23728 explicitly reduces only the constructor and
zero constants and passes2.44s/4302428KiB.23729 passes3.03s/4300888KiB: complete
source-model compression=closed owned reference,all slices and typed arity16,
without arithmetic/canonicality/output assumptions. Native association remains
separate and the timed-out Kani gates are never promoted to certificates.

23730 rejects an unused ExternalTypes requirement on a reused theorem.23732
proves the closed equality directly and passes2.06s/4303760KiB: fold/compression/
owned reference totality is independent of ExternalTypes and ExternalFuns.
23731 passes2.33s/4302576KiB: closed compression equality is consumed through
complete caller equality and BodyData.refinement_of_data. This transports the
source-model dictionary; it does not identify it with the live native dictionary
or discharge the remaining whole-data antecedent. All accepted reports standard.

## Actual iterator control continuation

Env-J 23748 (Outcome), 23749 (Cursor), 23750 (CursorLoop), and 23751
(IteratorSource) passed. These replay the small locally checked prerequisites
into the pinned host object environment and prove the exact emitted iterator
step and initializer, including full backing data and remaining-tail equality.
23752 was refused by the separate read-only reservation preflight at
17:26:12 UTC (projected 60,532,195,328 bytes > safe 59,055,800,320 bytes).
No compiler or capped scope started; zero attempts charged. The next attempt
will use a fresh ID after at least three minutes. No admission mechanism changed.
The composed native-control compression module explicitly retains association
of the original whole helper as a separate obligation; its source definition
is not the reference output, and it does not upgrade a Kani timeout to a pass.

### Quiet-window timing exception retained

The proof-local fission Aeneas probe was admitted at 16:50:18.455686 UTC,
inside the subsequently learned 16:50–17:20 cross-stream quiet window. It
failed in 0.386 seconds with `Not_found` in
`InterpReduceCollapse.collapse_ctx_following_sequence`; no whole-helper output
or certificate was accepted. The quiet hold became known at the 23739 launcher
refusal at 16:50:34. No further host capped scope was started until 17:21:32.
This timing overlap is retained as a deviation, not hidden as a successful
admission. The marker and launchers were never edited.

Timing deviation: retry 23753 began at 17:29:01.907652 UTC, 169.388 seconds
following refusal 23752, approximately 10.6 seconds short of the required
180-second wait. Admission allowed it and the shared launcher was unchanged,
but this does not satisfy the wait rule. This is recorded as a procedural
deviation, not described as a compliant retry. No resource caps were raised.

Read-only sibling refresh: pv-cb head
`93c41a0ab28add4dc08dde56ad957e62f5c30ef7` still labels op223/V240 OPEN
and op250/V257 SKIPPED (earlier sibling source-policy installation only).
No callback installation or sibling worktree modification was performed here.
The new local CursorFuel proof gives necessity as well as sufficiency of the
17-evaluation arity16 control bound for successful identity steps. CursorTrace
proves the instrumentation records every input exactly once in order and erases
to the same complete Outcome, including failures/divergence. Neither is a new
native Kani certificate or a source association for the whole Rust helper.

23754 was an aggregate-reservation preflight refusal at 17:29:20.221764 UTC;
zero Lean attempts. Fresh host compile 23759 began at 17:32:32.954111 UTC,
after 192.732 seconds, and failed only on a Lean notation-spacing error.
23760 corrected that source and passed; no unchanged failed compile was rerun.
The iterator-state Aeneas scope reached its internal reservation check at
17:37:00.159227 UTC and was refused on a racing removed cgroup path. The
translator did not run. Its next retry must be after 17:40:00.159227 UTC.

23778 was refused before compiler admission at 17:42:41.210373 UTC due to
aggregate reservation (60,532,195,328 projected bytes). It counts zero Lean
attempts. Next host attempt must have a fresh ID and begin no earlier than
17:45:41.210373 UTC. No source was sent or compiler launched for this ID.

## Local cached J checks during the second quiet window

23780 was refused by the shared launcher quiet guard before Lean; marker until
1793038500 (18:15 UTC). No host scope has been started since this was learned.
Local preflight IDs23781–23784 did not invoke Lean or write compile inputs;
they count zero. One lacked the local Std path. Later preflight source walks
followed repository baseline imports that differ from the pinned J objects.
The correct check pins existing J objects as objects and traverses newly added
PV_RW sources; it does not claim the baseline source files were recompiled.
The earlier description of missing cache objects was too broad: the1171-entry
23780 J object closure was already present and matched, requiring no refresh.

A read-only copy of the earlier pv-runjoin cached J backend/shared objects was
made under /private/tmp/pv-rw-step-native-local-20261026. Its Aeneas root SHA256
matches the live J backend, d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d.
Existing local mathlib source commit81a5d257c8e410db227a6665ed08f64fea08e997,
Lean kernel8c9756b28d64dab099da31a4c09229a9e6a2ef35; no dependency builds or
Linux native libraries. Each focused local attempt records its own source,
existing imported object hashes, compiler/Std/project pins, Result and axioms.
23785 passes the emitted combined transition control proof (40.36s,
2,848,800,768 RSS bytes,0swap).23786 fails on a namespace typo; corrected23788
passes the loop correspondence (43.34s,2,590,097,408 bytes,0swap).
23787 passes the full V163 component criterion (25.10s,2,952,921,088 bytes,0swap).
These are cached focused checks, not a frozen release/dependency source replay.

Final sibling read-only refresh: `codex/pv-cb-20261026` head
`575f9d5b9b014074c95f14bc06afdb9e541ee26b`; op223/V240 OPEN,
op250/V257 still SKIPPED (source policy only). No live installation here.

The LLBC basename resolver retains all six exact translator inputs and checks
shortened source filenames against the original receipt's full-path content
hashes. `llbc-source-resolution.json` resolves every recorded source binding;
it supplements, and does not modify, the conservative original receipt fields.
The fission translator failure remains a failure, with no accepted whole output.

Final audit preflight237/23807 (ID23807) refused locally before invoking Lean:
IteratorMeasure had been checked in23735 without an emitted object. Zero
attempts charged. The uncompiled two-stage audit proposal is archived verbatim;
no accepted leaf source changed.23808 emits that exact existing prerequisite
into the local pinned cache (3.33s,659,587,072 RSS bytes,0swap,standard axioms).
The last compile will combine the complete axioms audit and frozen focused
manifest into a single invocation. `final-focused-source-manifest-v2.json`
explicitly supersedes the preflight-only proposal, retaining its original pins.
