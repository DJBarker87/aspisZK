# Constructed protocol privacy endpoint — 2026-10-21

Branch `codex/cx-priv-endpoint-20261021`, base `b9c171232`.

## Stage 1: composed privacy specialization

`R1Z.PrivacyR1FinalProtocol.privacy_R1_protocol` specializes the unchanged
`PrivacyR1Final.privacy_R1_final` to `PhaseProtocolInstanceBin.baseWire` and
the composed `prover`. It removes the universal `R_causal_D80` by
`causal_premise`, the eight `R_commit_D80` families by the constructed
commitment grammar, and D/ι/hι/R_wire_Sem1Uniform by the concrete rows01,
algebraMap injection and sampler_source. Residual premises have the original
quantifiers, specialized to this instance. Typed read coverage is retained
in this stage pending the length/coverage check.

Env J attempt 9603: exit 0, wall 7.44 s, peak RSS 4,060,832 KiB, swaps 0.
Both theorem audits: `[propext, Classical.choice, Quot.sound]`.
Exact source revision/hash, dependency objects/fingerprint, full audits,
diagnostics and timing for attempts 9600–9603 are committed in
`endpoint-attempts-9600-9799.jsonl`. Earlier failures were notation elaboration,
AddressAt unfolding, and transport across non-definitionally-equal finite
universe instances; extensional finite-set equality fixes the latter without
enumerating any universe. No cap or heartbeat override was added.

No existing shared source/object was replaced except this branch's own new
endpoint drafts, snapshotted under `snapshots/codex-cx-priv-endpoint-20261021/`.
All attempts use run-joint.sh, env J, -M7000, MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0; the launcher reported 24 GiB populated plus 7 GiB.

## Stage 2: coverage, lengths and joint structural satisfiability

`PhaseProtocolCoverageBin` proves wide=32, semantic/opening exact D79/D81
widths, final=2048, C1=480, C2=128, folded=128 including padding. It proves
the existing framing codec equals the privacy grammar byte-for-byte and
constructs a typed transcript whose Rest equals recP.rest. Together with the
constructed commitment grammar and the ≤480 leaf bound, this proves D84
ReadCoverage at every answer vector, including inconsistent/exhausted ones.
The proof counts fixed-width vectors symbolically. It never evaluates a
large address/tape/answer universe, a field element, an FFT, or a recurrence.

The release endpoint now chooses `publicWidth = (base.pubBytes x).length`.
Thus the public-width fact is reflexive and **no ReadCoverage or public-width
premise remains**. The ROM table construction, qmax=2^64, address membership,
fixed transcript/leaf lengths and sampler are proved model components.
Other numeric premises refer to seed counters/tape dimensions and remain:
the constructor does not choose E₁/E₂, L₁/L₂, or tapeOf.

`PhaseProtocolConsistencyBin.construction_checks` proves coverage, commitment
grammar, universal causality, ROM budget, leaf lengths, decoder locality,
sampler-source equality and embedding injection **together** for every base
and seed satisfying the public-width fact. Its
`structural_hypotheses_inhabited` constructs an explicit finite residual base
and seed, and preserves a given valid witness of the public statement. It
therefore does not rely on an empty HonestProver.Instance or an assumed
inhabitant of the wire/prover structures. The witness uses empty public bytes
and a constant tape only to check structural consistency. It is not asserted
to satisfy the remaining uniform-tape, builder or source-execution premises.
This is the requested construction-owned non-vacuity check, not a proof that
all still-conditional deployed-source premises are jointly realizable.

Final focused targets (all env J; standard axioms only; swaps 0):

| Target | Attempt | Exit | Wall | Peak RSS KiB |
|---|---:|---:|---:|---:|
| R1Z/PhaseProtocolCoverageBin | 9611 | 0 | 4.60 s | 4,060,900 |
| R1Z/PrivacyR1FinalProtocol | 9615 | 0 | 11.71 s | 4,060,324 |
| R1Z/PhaseProtocolConsistencyBin | 9616 | 0 | 8.42 s | 4,048,608 |

Intermediate 9607, 9612 and 9614 were green predecessors. Attempts
9604–9606, 9608–9610 and 9613 retain their local elaboration diagnostics;
none failed for memory pressure. Fixes were explicit arithmetic/index
arguments, reduction of structure projections, precise list/byte transport,
and renaming a reserved identifier. No source was retried unchanged with
unchanged dependencies. Final consistency imports the final endpoint, which
imports the final coverage target; this is the focused dependent bridge.
No full frozen-manifest, Rust, SBF, runtime or reproducibility replay was
run: no source or artifact covered by those gates was changed.

## Verbatim release statement

The following context and statement are copied verbatim from
`lean/R1Z/PrivacyR1FinalProtocol.lean` (inside its namespace/noncomputable
section). The proof is the existing final theorem applied to the selected
instance, with the discharged proofs supplied. `publicWidth` and the outer
`seed` in the copied section context are used by commitment_grammar; the
release theorem binds its own seed at the exact public width and has no
exported publicWidth argument.

```lean
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final
local notation "K" => AspisWideTower.WideExact
variable {CommitHandle Aux : Type} {F : Subfield K}
variable (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
variable (seed : R1ProverP K CommitHandle Aux F (wire base publicWidth h B outputs x).toWire)

theorem privacy_R1_protocol
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
      h.public w = x.1 → ScanCoupling
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ScanCoupling
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x))) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454
```

## Remaining premise owners

Here W/Pr mean exactly the constructed wire/prover in the verbatim statement,
with K=WideExact and width=public-byte length. These names are only explanatory
abbreviations; they do not replace source hypotheses in Lean. Every retained
premise is the original premise verbatim after this specialization. Their
textual identity is checked by `audit-endpoint.py`.

| Remaining premise/input | Exact obligation at this instance | Owner |
|---|---|---|
| hB | `PackField B`. | Accepted algebra/packing model; SourceIdentification ties the source basis to B. |
| hpub | `PublicBase F x.1`. | Public statement/relation identification; SourceIdentification. |
| builder_refinement_D46_D51 | `BuilderSoundOn h B x`: actual public map, transport, build trace, baseTyped/lanes/helperSum/helperInactive, D50 sentinel. | Concurrent builder worker: BuilderSource / SourceIdentification / builder refinement. No files owned by that worker are changed here. |
| cF, R_commit_equal_fibres | Every tape τ has exactly cF successful preimages under the residual seed.tapeOf, over the full two answer-vector carriers. | SourceIdentification: tape distribution/uniformity, field guards and rejection. Successful fixtures do not prove equal fibres. |
| L₁, L₂, R_commit_exhaustion | Any tapeOf=None implies one of the two specified 16-try word-stream exhaustion events. | SourceIdentification: expander wordsE, actual decoder, guards/rejection and failure behavior. |
| R_commit_counter₁, R_commit_counter₂ | E₁≤2^64 and E₂≤2^64. | SourceIdentification: retained seed counters and complete expander read inventory. |
| R_commit_stream₁, R_commit_stream₂ | 16L₁≤8E₁ and 16L₂≤8E₂. | SourceIdentification: stream length/budget relation. |
| R_commit_cell_count | `RCommitCount L₁ L₂`, the binary layout cell envelope. | SourceIdentification / builder read accounting, including universal source read completeness. |
| R_commit_blocks₁, R_commit_blocks₂ | E₁≤2L₁ and E₂≤2L₂. | SourceIdentification: expander block budget. Not selected by PhaseProtocolInstanceBin. |
| R_wire_coin_carrier | W.Cm≃(RIdx→OracleAnswer), both inverse laws. Cm is retained from base. | SourceIdentification: commitment coin/backend representation. |
| R_wire_D80_batches | Two normalized transaction batches: concatenation, Nodup, exact openedQ coverage and fibre union. openFib/openList are retained from seed. | SourceIdentification / execution refinement: sort/dedup, paths, folded padding, first-read/address/answer preservation. |
| R_wire_D80_ordered_log | Equality of the complete ordered byte/answer lists for all w/sec/d/tape/roots/rest/ch. comLog is retained from base. | SourceIdentification / execution refinement. Set equality and a successful trace are insufficient. |
| source and finite/nonempty source.RealRand / source.IdealRand | The explicit source experiments and genuine finite randomness spaces. | SourceIdentification: adopted real and ideal programs and randomness. No concrete Rust experiments are supplied here. |
| observer_program | Operational query program for every source observer/view/log. | SourceIdentification / observer and backend execution correspondence; the Boolean decision map is already constructed. |
| R_wire_builder_checker_D75_retry | ScanCoupling of source real with the constructed model, per observer and valid witness. | SourceIdentification / builder refinement / execution refinement: all D75.4 checker inputs, builder-public-trace identity, P_chk→P_R1, no-pole↔VR1, retries, secret/tape law, output/failure publication and serialization. All non-query Semantic errors must agree or be impossible. |
| G_sim_R_wire | ScanCoupling of source ideal with the model using the same explicit simE. | SourceIdentification / simulator execution refinement: witness-free input, P-only retry loop, shifted payloads, programmed oracle, logs, tape law, output/failure bytes. |
| Actual-history and off-query agreement fields inside both ScanCoupling premises | ≤8 scan opportunities on each side, each actual reached-history event has the required probability bound; whole Boolean observations agree off their union. | SourceIdentification / query-history execution refinement: adaptive shared oracle, LE low-18-bit words, fresh-address/history transport, collision/prior-read accounting, first-stop and failure behavior. ROM uniformity alone does not prove this. |

## Rust-to-model joins (PHASE2-JOINS exact remaining scope item 2)

D88 moves these correspondences to **SourceIdentification / builder refinement**;
none is an extra causality hypothesis at this endpoint:

- Samplers: the extracted QM31 sampler/embedding, both circle block policies,
  ordinary wide opening blocks, nonzero gamma, field-carrier conversion,
  low-subfield guards, rejection and fallback/failure behavior.
- Query parser: eight little-endian words per block, low 18 bits, first 22
  distinct values, readiness/first-stop behavior, exhausted normalization,
  and the law at actual reached adaptive histories. The total mathematical
  decoder is not a proof that source QueryScan succeeds.
- Framing/serialization: source semantic/opening/final selectors, tags,
  length bytes, compact expansion, wide/low-lane encoding, public bytes,
  auxiliary/failure metadata and publication. The model's arbitrary Aux
  output is excluded from the encoder by construction.
- Leaves/FFT: exact initial-circle and final-line evaluators versus the Rust
  FFT, D18/S2 transport, coefficient ordering, slot/lane order, low-field
  guards, C1/C2/folded widths, folded data range and zero padding. Reuse of
  the extracted S2 index is not the full FFT correspondence.
- Commitment execution: the now-constructed eight grammar families versus
  actual hash calls, secrets/seed/salt scheduling, full read inventory,
  binary children/parents and folded geometry. AddressAt being definitional
  in this model does not establish operational source coverage.
- Execution refinement (PHASE2-JOINS item 3): addressed-call/answer and
  first-read preservation under permitted commutations; salt scheduling;
  normalization of unused query blocks; normalized batch and ordered-log
  equality; common backend/log oracle; retry/accept/failure/publication law.

The real coupling carries builder/checker and real execution joins; the ideal
coupling carries simulator/programmed-oracle joins. The original D75.4 named
checker input list in PRIVACY-FINAL remains required inside the real handoff.
The source-owner worker's theorems must identify these *same* residual
base/seed/h/B/outputs/x/source inputs; a proof about another trace or model
is insufficient. No implementation extraction, Kani result, ELF gate, or
source coupling is claimed by this endpoint work.

## Premises discharged at the release endpoint

| Original premise | Supplied model proof |
|---|---|
| R_causal_D80 | PhaseProtocolInstanceBin.causal_premise, at all answer vectors, using endpoint_wire's definitional specialization. |
| D / ι / hι / R_wire_Sem1Uniform | Constructed rows01, algebraMap from QM31 into WideExact, RingHom.injective, sampler_source. |
| R_commit_D80 (all eight families) | PrivacyR1FinalProtocol.commitment_grammar; toProver constructs caddr=gram. |
| R_wire_read_coverage | PhaseProtocolCoverageBin.read_coverage; fixed-width message/leaf proofs and framing equality; public bound is reflexive at the selected width. |
| Generic field/finiteness/M31-algebra instances | Concrete WideExact instances, not new assumptions. F/B/hB and public relation assumptions remain. |

ROM carrier/table/observer construction and adversary cap were already
removed by D84 in PrivacyR1Final; they are inherited, not counted as newly
closed source obligations. Source cap/backend correspondence is still part
of the operational joins above. No remaining numeric, tape, batch, log or
coupling premise is inferred merely from a constructor name.

## Stage 3: final evidence audit and checklist

`python3 r1p-final/audit-endpoint.py` is a read-only packet audit (run from
any directory using the script's full path). `endpoint-final-audit.json`
records the result: 17 assigned attempts, zero duplicate source/dependency
pairs, zero swaps in all attempts, zero mismatches against the launcher's
independent source SHA records, and all 21 new theorem audits contained in
the three current successful target receipts. Every axiom set is a subset
of `[propext, Classical.choice, Quot.sound]`. There are no forbidden proof
constructs or new heartbeat/recursion options. All final source hashes match
the compiled receipts, and object SHA256/size pins are recorded without
committing objects or binaries.

The audit compares 21 retained binders and the conclusion verbatim after
W/Pr specialization and whitespace normalization; the four source randomness
typeclass inputs are retained too. It checks the statement quoted above
against the actual source. PrivacyR1Final, PhaseProtocolInstanceBin and
BuilderSource are byte-identical to base b9c171232. The causal checklist row
in PRIVACY-FINAL now points to this protocol endpoint, with the generic
statement explicitly retained as historical/reference scope.

No work was stopped by a genuine obstruction. All three requested stages
are complete at the stated conditional/model scope. The remaining source
premises and Rust-to-model joins are enumerated above; none is claimed
proved by structural satisfiability. No push, merge, wallet/key operation,
existing Lean-module edit, or concurrent-worker-owned edit was performed.
