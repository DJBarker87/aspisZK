# V403 — focused stop at the op257 world child

**V403 remains OPEN. CLOSED-ON-CANDIDATE is not established.**
Candidate `d4ed1ba89f05a754d3982b9250f53acbd405ce7b`.
The caller/producer list was committed first, in `8f3ec49e22b`.
No complete recursive caller transport was attempted.

## Exact missing lemma

`PV_M31_NativeMapReplyFrame257` is the **proposed name of the missing lemma**,
not an existing declaration or an assumed hypothesis added to a theorem.
Its necessary scope is the actual C1 specialization of V263:

* Rust child `host_work::map`, `host_work.rs:10`, called from
  `host_sumcheck::prove_sumcheck_round`, `host_sumcheck.rs:82`.
* `T = Result<QM31, host_wire::Error>`, with the real Error's full variant
  set, not a reduced surrogate; `F` is the actual closure capturing
  `(oracle, point, round, assignments)` and invoking `evaluate_assignment`.
* Public round `r<10`, assignments `1<<(9-r)`, stage `100+r`,
  count `28*assignments`. Arbitrary child replies must include all raw QM31
  words and every Error. Neither successful oracle replies nor their
  canonicality may be assumed.
* For each actual admitted world execution of this frozen child: identify
  the exact returned vector, callback argument windows/captured values,
  caller-visible state frame and ordered effects with the child interpretation
  consumed by the ruling-(y) caller certificate. Retain allocation denial,
  thread creation failure, TLS initialization, join/panic propagation and
  abort/nonreturn branches. For the adopted panic=abort client, a panic is
  not a recoverable `Error` value invented by the harness.

This requires a **world-indexed reply/frame bridge**, or a proved world-indexed
local event projection sufficient for this caller. The existing pure external
type is only:

```lean
op257 {T F : Type} (inst : core.ops.function.Fn F Std.Usize T) :
  Std.Usize → Std.Usize → F → Result (alloc.vec.Vec T)
```

It has no world/state/effect coordinate. Its presence in ExternalFuns supplies
no instance of the required native bridge. The exact captured type is in
`inputs/op257.lean.txt`; this displayed binder-name abbreviation is explanatory.

## Why this is the specified stop

Ruling (y)(1) permits an unconstrained full-return oracle in the frozen caller;
it does not assert the oracle's actual native reply or erase its effects.
Ruling (y)(2) still requires the child's actual bridge and precise frame.
For this child, the retained evidence explicitly stops at that association:
`inputs/V263-prior-report.md` records only partition arithmetic theorems and
finite native validation. Recount11 V263 says the source interpreter/world
associations remain uninstalled, with OS/allocator/thread/stack failures
retained. See `basis.json#recount11/V263`.

The source confirms the boundary: native_workers.rs reads/writes ACTIVE TLS
(:5,15–20), chooses the nested/sequential branch (:31), spawns (:42), joins
(:47) and resumes a panic (:53). Under pv-common rdea-2/D567 these are stateful
world answers. Replacing them with a guaranteed-success pure callback would
not discharge this bridge. No writable-static Kani harness was introduced.

The **algebraic canonicality property itself does not need canonical map
replies**: interpolation normalizes arbitrary samples. A local value/event
projection might avoid proving map's full value law. Such a native
world-respecting projection/frame has not been supplied here, and this report
does not claim every possible V403 proof must prove all of V263. The stop is
specifically the unavailable actual-child certificate in the requested
full-Result/effects ruling-(y) substitution. Continuing by building that world
association would cross the user's explicit focus boundary.

## Before and after statements / premise accounting

Before, exactly as `PV_Canon_Deployment.lean` states:

```text
P_NativePrefixBinding base ops reached :=
  ∀ p q, reached p q →
    ∃ e : ExtractedPrefix base ops, e.coefficients = p ∧ e.read = q

reached_canonical (binding : P_NativePrefixBinding base ops reached) :
  ∀ p q, reached p q → Coeffs p ∧ Q q
```

`ExtractedPrefix` retains the actual selected interpolation, semantic,
array-update/readback equations and round<10. Its complete source is captured
in `inputs/PV_Canon_Deployment.lean.txt`. Coeffs/Q constrain the 112 coefficient
limbs and four challenge limbs, individually <2147483647.

**After: the identical statement and binding premise remain.** There is no
new theorem or native binding instance. Premises removed **0**, added **0**,
changed **0**, both at this theorem and at
`PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`. Quantifiers, carriers,
guards and conclusions are unchanged. The missing lemma above is a work item,
not an accepted trust item or a replacement premise. T remains precisely
entropy_law, entropy_kernel, observation.

V220's restored complete source/reference Result law is retained read-only
(`inputs/V220-prior-report.md`). It supplies neither a native C1 event instance
nor the op257 world frame. No Horner replacement was attempted, and the D234
noncanonical challenge is not claimed reachable.

## Validation and handoff

Ran the immutable-candidate source census, checked its 18 direct call sites,
captured the source/basis inputs and hashes, and checked Git whitespace and
change boundaries. These are **source inspection**, not machine proofs or
new native validation. Historical producer theorems were read, not recompiled
or re-audited; their historical `#print axioms` results remain summary-based.

New Lean launches **0/50**, Kani **0/30**, extractions **0/2**. No host scope,
cache modification, ELF build or manifest replay ran. Audit slots
92447–92449 remain unused. The budget is unspent because of the explicit
world-machine focus stop, not exhaustion or host failure. No new theorem
exists for an axioms audit; source-inspection axioms are N/A.

Next deliverable: supply the above **C1-specialized** op257 world reply/frame
bridge (or a world-respecting event projection) from the world line, then run
the frozen per-caller certificate with unconstrained full replies and matched
failing controls, substitute the actual producer bridges and discharge
P_NativePrefixBinding. Do not restart the failed recursive proof.
