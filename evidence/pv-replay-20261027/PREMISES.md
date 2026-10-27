# Headline premises retained by this dry replay

Snapshot: research b90540e01c10a102535dcc0c0b0c50fb18880e0f. This job changes no theorem, definition, quantifier, carrier, observer, bad event, conclusion, deployment condition or trust field. Removed/added/changed premises: **0/0/0**. Compilation and an accepted-axiom audit do not prove a supplied hypothesis.

## DeployedReal endpoint

`R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` retains the binder order `{CommitHandle Aux}`, `template`, `outputs`, `x`, `rust`, `[Fintype rust.RealRand]`, `[Nonempty rust.RealRand]`, `observer_program`, `refinement`. Its first conjunct is guarded by `∀ adv w, public w = x.1`; the other two bound the same numerical expression, finally below `2^-100`.

The substantive supplied proposition is `RustRealRefinement template outputs x rust observer_program`:

- For **every** adversary and canonical witness with matching public statement, supply `Nonempty (ProverCommitFuelJoin22.RunJoin runtime model old queries)`.
- The **same** coupling supplies `S`, `Fintype S`, `Nonempty S`, `toR`, `toM`, and exact rational-test marginal laws `meanR` and `meanM`. The model target includes its independent seed and fuel tape.
- Its `agreement` equates the complete runtime view **and observer decision** with the model outside the **fixed** union bad event. This is not merely acceptance equality. The event includes the existing parser events, seed-prefix guess and five-draw exhaustion; query functions are fixed by the model. No event or observer is weakened here.
- `rust` remains a free experiment parameter. This theorem does not construct the actual deployed instance, establish adversary/domain non-vacuity, identify the frozen binaries, or instantiate the native complete execution join.

Relevant ledger families remain V036 (runtime marginal), V037 (model marginal), V038 (agreement), V043–V044 (observer association), V045–V047 (deployed-instance/domain application gaps). Canonical builder/caller/fibre/exhaustion/budget facts used by the proof are existing derived mathematical facts, not newly discharged native implementation obligations. The `Admitted` namespace is a canonical admitted-domain specialization, not `sorry` or a new axiom.

## V2 alternatives

`R1Z.PrivacyR1HeadlineV2.privacy_headline_v2` retains:

1. `builder_premises : BuilderPremises h B x`, meaning `∀ w, public w=x.1 → PublicBase F x.1 ∧ BuilderSoundOn h B x`.
2. `R_commit_caller : ProverCommitCallerInstance.CallerLaw Pr` (fixed block counts and one shared quotient-coordinate equivalence with its decoder law).
3. `R_wire_builder_checker_D75_retry`, a quantified real `ModelExecutionJoin` under the same witness/public guard.
4. `G_sim_R_wire`, the quantified ideal `ModelExecutionJoin` against the unchanged mathematical simulator `simE`.

`privacy_headline_v2_fibres` instead retains the explicit constant-fibre cardinality law and `R_commit_exhaustion : RExh Pr L₁ L₂`, alongside builder and real/ideal join premises. Template, input, outputs, public statement, decoder and observer remain parameters. The replay removes none of these.

## Deployment boundary retained

The standing privacy ledger and owner decisions remain authoritative. This dry replay does not close: prover proved = prover shipped; E1/E2 native environment contracts; concrete deployed RunJoin and native Records/compiler/snapshot association; OS-failure option-B witness-independence/transport; inversion zero-boundary execution linkage; complete L1/L2/L3 limb/address/latency side channels and compiler preservation; client proof-account-route execution binding; final source/feature/toolchain/ELF adoption and final release replay.

The capped trust list stays **exactly** `entropy_law`, `entropy_kernel`, `observation` in `R1Z.PV_RunJoin_TrustItems`. No missing native proof is folded into that list. V371 remains a substantive trust item under Secure Boot lockdown. No target is established by this coherence exercise.

Source references: `PrivacyR1HeadlineDeployedReal.lean` (`RustRealRefinement`, `privacy_headline_deployed`), `ProverCommitFuelJoin22.lean` (`RunJoin`), `R0Z/FsAbort.lean` (`Coupling`), `PrivacyR1HeadlineV2.lean` (both endpoints), `PrivacyR1Headline.lean` (`BuilderPremises`), `ProverCommitAdmittedEndpoint.lean` (canonical builder derivation), and `design/PRIVACY-LEDGER-20261026.md` at the pinned research revision. Exact resolved paths and SHA256 values are in replay-plan.json.
