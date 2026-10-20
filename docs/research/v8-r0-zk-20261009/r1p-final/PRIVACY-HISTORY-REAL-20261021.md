# Real privacy history — 2026-10-21

Branch `codex/cx-priv-history2-20261021`, base `de2dd2c8b`.

## Stage 1: whole-run repeated-read obstruction

The literal requested exclusion is false. An event covering **every repeated
read over the whole real run** cannot have small birthday mass. The retained
`OProg` allows `.query a (fun _ => .query a (fun _ => .done))`. This is a
legal, answer-insensitive two-read adversary under the fixed `2^64` observer
budget. It is independent of the proof, instance, honest success and oracle.
The address can be `[]`, which is in every finite-ROM domain.

`QueryScanWholeRunRepeatObstruction.real_game_repeats` proves this for the
exact `GamesR1PBin.realGameP`, in both `firstGood` branches. Its returned
`observerOracle` includes the repeated suffix. These are actual reads of
the complete run. `covering_event_mass_one` proves that **any** event covering
these repeats has mass exactly one, on any finite nonempty random carrier.
`no_small_covering_event` rules out every proposed bound κ < 1, including any
κ for which the requested positive total is below `2^-100`.

This refutes the whole-run *event specification*, not privacy and not a
collision theorem about distinct first-read addresses. In particular,
`BinCombinedMerkleCollision.mass` controls `hitsBad` on **first reads**; its
six-target term is not a theorem bounding deliberate address repeats. Reusing
it for the event requested here would be an event-identification error.

Focused env J 9824: exit 0, wall 1.97 s, peak RSS 3,512,380 KiB, swaps 0.
All five audits use subsets of `[propext, Classical.choice, Quot.sound]`.
9823 records two elaboration errors, repaired by symbolic successor
normalization and reducing let bindings before the match split. No large
carrier or recurrence was evaluated. Full fields, source revision/hash,
dependency fingerprint, exact target, errors and audits are preserved in
`history-real-attempts-9800-9999.jsonl`.

## Remaining work and endpoint status

The requested endpoint is blocked by the event specification above. Existing
modules are unchanged. No theorem named `privacy_R1_protocol_history_real`
is asserted, and no probability hypothesis is disguised as execution data.
A sound next specification must distinguish repeats that invalidate a scan
word's first-read sampling law from benign verifier/observer repeats. It must
prove that each *scan* reuse implies one chosen first-read collision/target
hit, then transport the fresh lazy words and charge that single fixed event
once. Post-proof observer repeats alone cannot belong to that excluded event.

## Stage 2: exact real carrier and independent numerical check

`QueryScanWholeRunRepeatReal.finite_real_repeat_mass` specializes the
counterexample to the retained `fsR1P.RealRand`, a uniform finite table times
eight attempt-secret tuples. It is an unconditional mass-one result for any
honest prover, instance, public statement and acceptance predicates. It uses
the exact `RomFiniteBin.wire` budget, symbolically proving `2 ≤ 2^64`, and
proves `[]` belongs to every finite-ROM domain. It therefore applies to the
constructed phase protocol as a specialization, with no change to its parser,
source joins or builder assumptions. Adding output collisions, self-loops or
prior-read events by union cannot decrease this mass-one exclusion.

Env J 9825: exit 0, wall 1.87 s, peak RSS 3,507,464 KiB, swaps 0; all four
audits use standard axioms. An unused-section-variable linter warning does
not affect the statement or proof.

`QueryScanHistoryRealNumerics` proves the **independent numerical** portion:

- `kappa q = 6 * (q : ℚ)^2 / 2^256`; coefficient `c = 6` matches the
  five-reader-plus-output coefficient of `BinCombinedMerkleCollision.kappa`.
- The candidate *numerical* budget envelope is `q ≤ 2^65`. This packet does
  **not** assert a theorem bounding all actual run reads by that envelope.
- Symbolically, `kappa (2^65) = 6 / 2^126` and `kappa q ≤ 1 / 2^109` under
  that envelope. The proof is monotonicity plus exponent splitting.
- For any κ ≤ 2^-109, the proposed total is at most `4 / 2^109 = 2^-107`,
  which is strictly below `2^-100`.

This validates numerical slack; it does not supply the false event-mass law.
No claimed endpoint follows from this conditional numerical fact.

Final env J numerical attempt 9828: exit 0, wall 2.04 s, peak RSS
3,521,588 KiB, swaps 0; all six audits use standard axioms. 9826/9827 retain
elaboration failures. The final proof uses explicit addition monotonicity;
it neither normalizes the 454-bit term nor enumerates a carrier. Earlier
9826 emitted a threshold warning during arithmetic preprocessing; that tactic
was replaced rather than increasing any threshold or resource limit.

## Stage 3: joint impossibility, exact signature status and final audit

`QueryScanHistoryRealSpecificationObstruction.no_whole_run_exclusion_with_requested_total`
combines the two requested claims and refutes their conjunction on the actual
finite-ROM game. Its κ is arbitrary, so choosing a larger coefficient or
budget cannot evade the contradiction while retaining the final target.

Env J 9829: exit 0, wall 1.71 s, peak RSS 3,513,484 KiB, swaps 0; both
axioms audits use `[propext, Classical.choice, Quot.sound]`.

### Signature diff

There is **no implemented changed privacy endpoint**. The existing
`PrivacyR1FinalProtocolHistory.privacy_R1_protocol_history` remains byte-for-byte
unchanged. The exact endpoint-file diff against the assigned base is empty:

```sh
git diff de2dd2c8b -- docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1FinalProtocolHistory.lean
```

The desired deletion of `real_model_history_law`, replacement of arbitrary
`realBad` by fixed events, and addition of a once-charged κ are **blocked**,
not represented by an unproved or strengthened-assumption endpoint. In
particular, the existing `ModelExecutionJoin` cannot merely be converted to
`ScanCoupling` by citing the numerical lemma: it needs the disputed real
mass law, and its unchanged eight events have no additional once-charged
whole-run collision slot.

Before, verbatim critical real-model binders:

```lean
    (realBad : source.Adversary → h.Instance → Fin 8 → (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')).RealRand → Prop)
    (real_model_history_law : ∀ adv w, h.public w = x.1 →
      ∀ i, eventMass (realBad adv w i) ≤ scanProbability)
```

After, verbatim actual binders (unchanged; no discharge claimed):

```lean
    (realBad : source.Adversary → h.Instance → Fin 8 → (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')).RealRand → Prop)
    (real_model_history_law : ∀ adv w, h.public w = x.1 →
      ∀ i, eventMass (realBad adv w i) ≤ scanProbability)
```

Verbatim new compiled obstruction signature (this is not a privacy endpoint):

```lean
theorem no_whole_run_exclusion_with_requested_total
    (base : R1Wire K CommitHandle Aux) (bound : ℕ)
    (Pr : R1ProverP K CommitHandle Aux F (RomFiniteBin.wire base bound))
    (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (E_coll : (fsR1P (RomFiniteBin.wire base bound) Pr 8 (by decide) P Vp).RealRand → Prop)
    (covers_repeats : ∀ r, repeatedRead (realGameP (RomFiniteBin.wire base bound) Pr 8 P Vp
      h B outputs (repeatAdversary []) x w r).observerOracle → E_coll r)
    (κ : ℚ) :
    ¬ (eventMass E_coll ≤ κ ∧
      1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 + κ < 1 / (2 : ℚ)^100)
```

### Disposition of the requested stages

| Requested fact | Result |
|---|---|
| Fixed fresh-scan event plus E_coll covering all whole-run repeats | The whole-run coverage requirement has a compiled counterexample. |
| Fresh scan failure mass ≤ scanProbability, with prior-read transport | Not discharged. Existing independent LE law remains valid, but does not identify fresh coordinates of this run. Dependent item stopped after the exclusion specification was refuted. |
| E_coll mass ≤ c q² / 2^256 | Refuted for every κ < 1 if E_coll covers all whole-run repeats. Actual repeated-read event has mass one on the exact real carrier. |
| Endpoint without real_model_history_law, error increased once | Not asserted. A sound narrower event and revised execution join are still required. |
| Numerical total below 2^-100 | Proved independently for c=6 and q≤2^65; no actual whole-run budget theorem or mass theorem is claimed. |

The possible repair is **scan-specific freshness**, not a global prohibition
of repeats: restrict the event to first-read collisions/target hits that can
invalidate query-word freshness, prove that every problematic *scan* reuse
implies that event, and retain ordinary memoized rereads. Then identify the
conditional fresh coordinates through prior reads, apply the retained LE
independent-word scan law, and compose agreement with a single whole-run
collision event. This packet neither refutes that narrower repair nor
silently substitutes it for the stronger requested event.

### Evidence and repository audit

`python3 docs/research/v8-r0-zk-20261009/r1p-final/audit-history-real.py`
passes: seven new assigned attempts 9823–9829, four final compiled modules,
17 theorem audits, standard axioms, zero swaps, source/dependency SHA256 pins,
compiled object SHA256 and size only, and all 280 pre-existing PRIVACY Lean
modules unchanged against `de2dd2c8b`. Prior attempts 9800–9822 remain intact;
there are no duplicate attempt IDs or unchanged source/dependency retries.
`history-real-final-audit.json` contains exact final targets, exit, wall,
peak RSS, swap, source revision/hash, dependency fingerprint, object pins and
full axioms lines; `history-real-attempts-9800-9999.jsonl` retains every failure
and raw launcher/time output as well.

All compiles ran on the build host using `run-joint.sh`, env J, `-M7000`,
MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0. Recorded populated reservations
were 24–26 GiB plus this job's 7 GiB. Only these new modules were installed;
revisions of this branch's own drafts/objects were snapshotted under
`snapshots/codex-cx-priv-history2-20261021/<attempt>`. No existing shared
dependency was replaced. The last new focused theorem is the final dependent
bridge; the frozen manifest and generated certificates were unchanged, so no
unchanged complete regression was repeated.

No protected endpoint, BuilderSource, SourceIdentification, builder refinement,
Rust harness, or wallet key was edited. No push or merge was performed.
