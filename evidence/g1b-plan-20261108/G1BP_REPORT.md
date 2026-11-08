# G1BP: plan for the G1b field (TAS `NMS_Roots.r241`)

Target not yet established. This is a read-only audit and plan at research tip
96899e6f8eb. No merged module was edited and nothing was built on the host. The
only Lean that ran is a core-only stand-in, described in section 7.

## 0. Summary

The current field premise `Refines064 V0 I.f064 R0 w`
(TAS_Interfaces.lean:161-164, 237-239) has the wrong shape for the credited
TX2:241 implementation. `NMX_R9_StageTwo.stage2` never calls a function-shaped
064 constant, so no premise about `I.f064` can reach its proof. The shape that
matches what the implementation does is relational inclusion of the canonical
law, `LawRefines`. Under `LawRefines`, both branches of the literal stage2 close
by reusing merged generic folds, without Root0 and without the trace association
`at_actual`.

`LawRefines V0 True wEnv` (or `wAny`) is **not** provable from merged results,
and it is plausibly false off Root0. So the weak G1a law should become the
canonical law itself with Root0 dropped (`w := V0.tx2auth`). All G1a consumers
still close from that law, with one new value-level lemma that rests on the
merged `NNS_064Value.common_result`. There are two owner-visible points
(section 6).

## 1. Q1: is relational law inclusion the right G1b premise?

Yes. The proposed definition is:

```lean
def LawRefines (V0 : V2Lib) (R0 : Bytes → Bytes → Prop)
    (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)) : Prop :=
  ∀ (x : Bytes × Bytes × Bytes) (env : Env) (o : Obs (Except V0.VErr Unit)),
    Dom064 (lib V0 R0 w) x → V0.tx2auth x.1 x.2.1 x.2.2 env o → w x.1 x.2.1 x.2.2 env o
```

Why this shape is right:

- The 241 reference reaches 064 only through
  `Spec.call (Dom064 V) (fun x => V.tx2auth …)` (RSL_TX2_241.lean:95-96).
- `Spec.call` is `dom a ∧ law a e o` (RSL_Base.lean:223-224).
- The represented branch's 064 child is the whole relation
  `NMX_R7_VerifierSource241.meaning = Spec.map raw (LIBB_ObservationModel.law …)`
  (VerifierSource241:16-17).
- `stage2` takes `Classical.choose` over the full native meaning
  (NMX_R9_Live241:65-68). Nothing is known about the chosen 064
  sub-observation except that it is in the law.

Transport therefore needs every law observation on `Dom064 (lib V0 R0 w)` to be
in `w`, and that is exactly `LawRefines`. It is also exactly the merged generic
relational packet. With `verify := fun x => V0.tx2auth x.1 x.2.1 x.2.2`,
`NMX_R7_RelVerify241.RelPacket (lib V0 R0 w) verify` is equivalent to
`LawRefines V0 R0 w` (stand-in `relPacket_iff`).

The two premises are incomparable, so this is a change of premise, not a
weakening. Refines064 at a single function does not give `LawRefines`
(stand-in `cm_not_law`, a two-point counter-model; this is the content of
`NNS_SelectionObligation.packet_transport_iff`). In the other direction,
`LawRefines` says nothing about `I.f064`.

Dependence table (NNS_DEPENDENCE.md rows). No NMX_R7/R8/R9 file mentions
Root0 (grep). Root0 enters only through D2, via the generic
`NMS_R2Domains.entered`, which yields `R0` at `lib V0 R0 w`.

| Lemma | Uses canonical tx2auth how | Root0? | Under `LawRefines` |
|---|---|---|---|
| VerifierSource241.full (:27-33) | meaning ⊆ V0.tx2auth via `LIBB_Tx2Auth.same` | no, unconditional | reused unchanged |
| VerifierSource241.live (:35-38) | `contains_graph`, every input | no | reused |
| R8_VerifierUse241/Encoded/Reads/After/ValidateUse, R9_Head241.full | native ⊆ the canonical relational replay; target-independent | no (Head241.full:10-15 takes no domain) | reused unchanged |
| R8/R9_RelReplay241.fold (R9:19-27) | fixed `V := V0`, reflexive RelPacket `fun _ _ => refl _` | D2 only, generic | **replace** with the generic `NMX_R7_RelValidate241.fold L (lib V0 R0 w) verify packet` (RelValidate241:13-17), packet from `LawRefines` |
| R9_Native241.full (:23-34) | calls the R9 fold at V0 | D2 only | **restate** at `lib V0 R0 w` |
| Verify241.packet (:20-26) | statement assumes `Dom064 V0` (includes V0.Root0), but the proof never uses it (`contains_graph`) | no in the proof; yes in the statement | **new** 8-line domain-free copy `verify_law` |
| R7_Fold241.fold (:11-20) | fixed V0 | D2 only | replace with `NMS_R2Fold241.fold` (generic in V, :10-27), already used by `NNS_PortLaw241.root` |
| PortLaw241.*_member (:9-80) | membership in the replay at V0 | no | reused through `NNS_LibraryContext.replay`/`after_validate` (merged) |
| PortLaw241.canonical, StageTwo.root | V0 roots | D2 | **restate** (section 4) |

## 2. Q2: is `LawRefines V0 True wEnv` (or `wAny`) provable?

It is not provable from merged results, and I expect it to be false off Root0.

**Direction.** `LIBB_Tx2Auth.native` (LIBB_Tx2Auth.lean:78-98) and
`LIBB_ObservationFold.tx2` (:100-147) prove native ⊆ law. Both take Root0:

- `LIBB_Tx2Domain.domain` includes `LIB_Root0.root0` (LIBB_Tx2Domain:9-11).
- `common` uses `domain.root0` (:145).
- `resolved_details` and `stopped_details` (:20-47) pass Root0 into
  `NLT_CompleteRoot.root` and `NLT_C04Installed.at_event`.

`NNC_ObservedLaw.contains_native` (:20-28) and `NNC_064Weak.root` put native
outcomes into `w`. `LawRefines` needs the converse, law ⊆ native-observed, and
no merged theorem proves it.

**Over-approximation.** `LIBB_ObservationModel.law` (:23-26) differs from
`NNC_ObservedWeak.Observed` (:19-22) in three ways:

- (a) The resolved arm renders each C04 event as
  `LIBB_C04LogGraph.render (NLP_C04Chronology.atEvent (H env) …)`
  (LIBB_Tx2EnvTrace:15-16). That is the source plan built from
  `NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)` (NLP_C04Chronology:10-14).
  `w` instead renders native records (`NNC_RecordTrace`).
- (b) `Pieces` admits, for every failing C04 event, both the full rendering and
  any `Prefix` with `∃ answered parts, NLL_Prefix.At …` (ObservationPieces:10-20).
- (c) The stopped arm admits an abort at every merkle event of the source trace
  (ObservationModel:16-21).

The plan and the native child agree only through `NLP_C04All.Clause`
(NLN.BatchPacket). Its only producer, `NLP_C04AtActual.packet` (:12-25),
consumes `root0Input` in `NLP_C04Roots.bindings`. So off Root0, (a) is
unassociated, and (b) and (c) need native completeness, which also does not
exist.

**Check that would settle it.** Either prove a Root0-free
`NLN.BatchPacket H pr (parsed pr (root1 p)) p folded 1` at entered events, or
exhibit a proof/checkpoint pair where `root1 p` differs from the checkpoint
roots and the C04 child history differs from `atEvent`. Even a positive answer
leaves the completeness for (b) and (c).

**`wAny`.** It existentially binds the world and changes nothing about (a)-(c).

**NNH side.** `NNH_064WeakField.w`, `.weak` (:8-36), `NNP_HostIdentity.host_law`
(`wEnv frame = NNH_064WeakField.w`, rfl, :8) and `NNH_G1aEnv.field` put the
**host** `f064` in `wEnv`. None of them touch the credited stage2. They are not
needed for G1b in the proposed design. `NNH_G1aEnv.okHeader` (:12-29) is reused
in section 4 through its underlying `NNH_064EnvHeader.native`.

**Consequence.** Choose `g.w := V0.tx2auth`, so the weak library is
`lib V0 (fun _ _ => True) V0.tx2auth`. Then `LawRefines` is `fun _ _ _ _ h => h`
(stand-in `law_weak`). `NNC_G1a.weak` (`Refines064 V0 I.f064 True V0.tx2auth`)
would need the host f064 inside the law off Root0. That is the same blocked
trace association, so the `weak` field must be replaced (section 4).

## 3. Q3: the fallback branch (F2)

The obligation is `VerifyPacket (lib V0 R0 w) NMX_R7_Verify241.verify`:
`∀ x env, Dom064 (lib V0 R0 w) x → w x.1 x.2.1 x.2.2 env (verify x env)`
(NMS_R2Replay241:10-11). That is
`Refines064 V0 (fun p q r env => verify (p,q,r) env) R0 w`, the premise of the
merged `NNS_PortLaw241.root` (:21-27). That theorem already gives
`RowSpec_241 L D (lib V0 R0 w) (NMX_R7_Port241.stage2 ch)`.

From `LawRefines` the obligation follows with a single application:
`h x env (verify x env) d (verify_law x env)` (stand-in `packet_of_law`). The
lemma `verify_law` is the body of Verify241.packet without its domain argument.

`NMX_R7_PortLaw241.canonical` uses Root0 **only** through the 064 law
statement (`Dom064 V0`) and D2. It does not use `at_actual`. `NLP_C04Chronology.at_actual`
and `NLP_C04All.source` (Root0 at :53 and :17) were needed only to equate
`verify` (`LIBB_Tx2EnvTrace.observation`) with the host `NNH_064Install.f064`
(`NNH_064Execute.observation`), so that the old premise about `I.f064` could be
used. Under `LawRefines` that equality is unnecessary, so F2 disappears. No
Root0-free replacement trace (NNC_064Weak, NNH_064SourceDetails.trace,
NNH_MerkleBatchTrace) is needed.

## 4. Q4: proposed interface and consumers

### Consumers of `r241`

The only consumer is `TAS_Top.entryRoot` (TAS_Top.lean:50-58), at two instances:

- `weakEntry` (:70-78) at `(True, g.w)` with `g.weak`. Its users are
  TAS_Top.top (:142), asq8Frame (:93-100), EVB_EventB top_splitB (:205, :212)
  and the full top (:268, :275), TAS_TopB_NNE (:51, :62), and
  phys-adapter NNE_TopSplit (:37). TAS_TopB.top_splitB reaches it through
  `EVB.top_splitB_full` (TAS_TopB:158).
- `canonicalRef240` (:81-90) at `(V0.Root0, V0.tx2auth)` with `nmn.r064`. Its
  users are TAS_Top (:158), EVB (:220, :283), TAS_TopB_NNE (:70), NNE_TopSplit (:56).

What each consumer needs from the weak instance:

- stage1Ref and reject: independent of 064.
- asq8Frame: `WriteFree w` (through nmv.g2).
- NMF′B: an Ok 064 sub-observation implies a native accepted run (host
  `NNC_NMFB.root0_or_rec` :17-66 takes `native … (.resolved (ok (.Ok ())) records)`).

Field-type mentions to update: NNS_Field.lean:34, LIB_FullInstances.lean:48,
NFB_BinderGroup.lean:111 (`tG1a` copies `weak`), NNH_G1aEnv.field :35-40,
NNH_WeakEntryNative.produce :38-60 (RowSpec at `LIBB_V2Star.weak`, fixed H; no
consumer), and TAS_WIRING.md:62.

### Proposed definitions

These go in a new module (call it NNT_Interfaces). TAS files are not edited.

```lean
def LawRefines … (as in section 1)
theorem lawRefines_canonical (V0) : LawRefines V0 V0.Root0 V0.tx2auth := fun _ _ _ _ h => h
theorem lawRefines_weak (V0) : LawRefines V0 (fun _ _ => True) V0.tx2auth := fun _ _ _ _ h => h

structure NMS_RootsL where
  r242 : TX2_233.RowSpec_233 L D I.f233 → TX2_242.RowSpec_242 L D I.f242
  r241 : ∀ (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)),
    LawRefines V0 R0 w → TX2_242.RowSpec_242 L D I.f242 → TX2_241.RowSpec_241 L D (lib V0 R0 w) I.f241

structure NNC_G1aL where              -- replaces NNC_G1a; `weak` → `lawRefines`
  w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)
  lawRefines : LawRefines V0 (fun _ _ => True) w
  writeFree : ∀ p q r, WriteFree (w p q r)
  okHeader : (unchanged statement, TAS_Interfaces:286-287)
```

The composition changes are:

- `entryRoot` takes `h : LawRefines V0 R0 w`.
- `weakEntry` uses `g.lawRefines`.
- `canonicalRef240` uses `lawRefines_canonical` and drops `nmn`.

NMV, NMW, G2, NMF′B, A1-A5 and every RowSpec stay unchanged. The before/after
statements of the field are identical except that the premise
`Refines064 V0 I.f064 R0 w` becomes `LawRefines V0 R0 w`. The quantifiers,
carriers, failure events and conclusion do not change. The minimal alternative
is two fields, `r241c : RowSpec_241 L D V0 I.f241` (the existing
NMX_R9_StageTwo.root) and
`r241w : RowSpec_241 L D (lib V0 True V0.tx2auth) I.f241`. The parametric form
costs the same proof and I recommend it.

### Lemmas: reuse and new proofs

| # | Lemma | Sketch / reuse | Size |
|---|---|---|---|
| L1 | `NNT_Verify241.verify_law : ∀ x env, LIBB_Tx2Auth.law x.1 x.2.1 x.2.2 env (verify x env)` | copy of Verify241.packet (:21-26) without the domain | 8 |
| L2 | `NNT_Port241.root : LawRefines V0 R0 w → RowSpec_242 L D (validate ch) → RowSpec_241 L D (lib V0 R0 w) (NMX_R7_Port241.stage2 ch)` | `NNS_PortLaw241.root ch R0 w (fun x env d => h x env _ d (L1 x env)) h242` | 10 |
| L3 | `NNT_RelReplay241.fold (a) (domain : Domain (lib V0 R0 w) a) (h : LawRefines V0 R0 w) : Refines (NMX_R9_RelReplay241.replay a) (Ref L D (lib V0 R0 w) a)` | copy of R9_RelReplay241.fold. Packet = `relPacket_iff.mpr h`. Rewrite replay with `NNS_LibraryContext.after_validate` (merged); template is NNS_RelReplay241.fold :18-32 | 30-45 |
| L4 | `NNT_Native241.full` | NMX_R9_Native241.full :29-34 with L3 in place of the R9 fold | 15 |
| L5 | `NNT_Root241.parametric ch R0 w (h : LawRefines V0 R0 w) (h242) : RowSpec_241 L D (lib V0 R0 w) (NMX_R9_StageTwo.stage2 ch)` | NMX_R9_StageTwo.root :23-37 with L4 and L2. `weak_instance` and `canonical_instance` are one-liners. Canonical check: type is rfl with `lib_canonical` | 30 |
| L6 | `NNT_Field.r241 : NMS_RootsL…r241` at `install I0 ch` | `fun R0 w h r => L5 ch R0 w h r` (I.f241 literal; NNS_Field:34 checked the shape) | 10 |
| L7 | `NNT_LawOk.native_of_ok (env) (pub proof ck : Slice U8) (len : proof.val.length = 57607) (world) (o) (h : LIBB_ObservationModel.law pub proof ck env o) (ok : o.exit = .ret (.ok ())) : ∃ records events, NMN_064.Native (H env) ⟨⟨digest env,pub,proof,ck,()⟩,world⟩ (.common (.resolved (ok (.Ok ())) records)) events` | Case on parse: non-Ok gives `o = observation` with an abort/error exit (observation_exit :43-46). Ok: the stopped arm aborts; the resolved arm gives `common env … = ok (.Ok ())`. Then `NNS_064Value.common_result` (merged, Root0-free) and `NNH_064Execute.outcome`/`native` (:13-49) | 60-90, the only genuinely new mathematics |
| L8 | bytes form of L7 and `NNT_G1aLaw.okHeader` | `LIB_Bytes.fromBytes`, `NNH_064WeakField.fits`, then L7, then `NNH_064EnvHeader.native` (as NNH_G1aEnv.okHeader :26) | 40 |
| L9 | `NNT_G1aLaw.field : NNC_G1aL` with `w := V0.tx2auth`, `lawRefines := rfl-proof`, `writeFree := LIBB_V2Star.writeFree`, `okHeader := L8` | assembly | 15 |
| L10 | `NNT_WeakEntryLaw.produce` | NNH_WeakEntryNative.produce without `trace/source/rendered`; `NNH_Entry241.weak` and `NNH_RSLReads.from_reference` are generic; finish with L7 | 50 |
| L11 | `NNT_TopL`: TAS_Top/EVB composition restated over `NMS_RootsL`/`NNC_G1aL` (stand-in level, mirroring TAS files) | copy and edit three lines | 100-200 |

L3 has a definitional-unfolding risk: `{V0 with …}` projections inside
`afterValidate`. The merged NNS_LibraryContext already handles it with `simp
only [map_error]`, followed by `rfl`.

## 5. Q5: the closed canonical rows

They are not affected. FIN_240.candidate (:31-35) applies
`NMV_ConcreteWindows.root240 L D V …`, which is generic in V, to
`NMX_R9_StageTwo.root`. That root has no premise on any f064 and takes the law
as its 064 child by construction. FIN_221 (:29-33) and FIN_213 (:26-29) are
generic folds (`NVR_Folds`) at the same V0. FIN_333 and FIN_330 are the same
Props (TAS_Top:61-67). None of them consumes `Refines064` or `r241`. The
obstruction lives only in transporting the 064 premise into the
library-parametric field.

## 6. Owner-visible points

The proposal changes no RowSpec, trust row, adversary or probability statement.
The two points below go to the owner through the lead.

1. **TX2:064 leaves the top composition.** With `LawRefines`, `canonicalRef240`
   no longer uses `NMN_Root.r064`, and G1a no longer mentions `I.f064`. The
   connection between the 064 law and the deployed call then rests on A2
   (`NND_A2`, op11 at V0; TCK_REPORT row 144), as it already does for the
   credited 241. The theorem gets stronger (one hypothesis fewer), but the set
   of ledger rows feeding the headline changes. Record this. Do not present it
   as a premise removal.
2. **Off-Root0 fidelity of the credited stage2 (AGENTS §4).** On every input,
   stage2 represents its 064 child by the canonical source law. Off Root0, the
   actual 064 is proved only in `wEnv` (NNH_064WeakField.weak), and the law's C04
   event rendering is not associated with native records. The weak-instance
   consumers use only write-freedom and the Ok exit. The Ok exit is associated
   value-level and Root0-free (L7 through `NNS_064Value.common_result`).
   Event-level native association at the TX2 occurrence off Root0
   (`NNH_WeakEntryNative.Packet.rendered`, currently unconsumed) is unavailable
   under any field shape for this credited stage2. It would need a Root0-free
   C04 packet, or a re-credit, which is an owner decision. TCK_REPORT §2.4's G1b
   design assumed that "the actual 064 call refines". That assumption is false
   for the credited stage2, and the report should be annotated.

Status of the remaining work:

- The okHeader `Oracle` situation and RZ-STATE are unchanged.
- `TOP:G0` remains OPEN.
- Target not yet established.

## 7. Stand-in check

File:
/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/g1b-plan/G1BP_StandIn.lean.
Output: G1BP_StandIn.out in the same directory.

The check ran core Lean v4.31.0 (`lean` on one file): 0.2 s, about 400 MB RSS,
exit 0. The stand-in uses abstract Bytes/Env/RowSpecs and the exact
`lib`/`Dom064`/`Refines064` shapes. It checks:

- `law_canonical` and `law_weak` (reflexive instances);
- `packet_of_law` (fallback packet);
- `relPacket_iff` (LawRefines equals RelPacket at lib);
- `cm_not_law` (Refines064 does not imply LawRefines; axiom `propext` only);
- `entryRoot`, `canonical240` and `weak240` (new wiring without `nmn` or
  `G1a.weak`).

All other roots print "no axioms". This checks shapes only, not the RSL/NMX terms.

## 8. Codex brief (NNT_)

> **NNT_ (evidence/g1b2-20261108).** Deliver the G1b field at the literal credited `NMX_R9_StageTwo.stage2` under the relational premise `LawRefines` of evidence/g1b-plan-20261108/G1BP_REPORT.md §1/§4. Write new modules only: NNT_Interfaces, NNT_Verify241, NNT_Port241, NNT_RelReplay241, NNT_Native241, NNT_Root241, NNT_Field, NNT_LawOk, NNT_G1aLaw, NNT_WeakEntryLaw, NNT_TopL. Prove L1-L11 in order and compile each smallest module first. Reuse merged NNS_PortLaw241.root, NNS_LibraryContext, NNS_064Value.common_result, NMX_R7_RelValidate241.fold, NMS_R2Fold241.fold, NNH_064Execute.native and NNH_064EnvHeader.native unchanged. Never edit merged modules (TAS_*, EVB_*, NMX_*, NMS_*, NNS_*, NNH_*, LIBB_*). Never change a RowSpec, Dom064, the credited stage2/Impl, trust, adversary or H. Never add Root0, hash injectivity, success, representation or a hypothesis that states the conclusion. If L3's defeq fails, use NNS_LibraryContext rewrites; do not change the target. If L7 needs anything beyond the parse/arm case split plus common_result, stop and report the exact missing lemma. Do not attempt `LawRefines V0 True wEnv`; it is out of scope (G1BP §2). Host: NUC build host only; one serial capped scope at a time, `MemoryHigh=6G`, `MemoryMax=8G`, `MemorySwapMax=0`, tasks64; Lean `-M7000`, async=false, 180 s per file. Seed by prepending the NNS export (`…/codex-cx-g1b-20261108/NNS_objects_v2`, `NNS_primary`, then the exact LEAN_PATH in evidence/g1b-20261108/NNS_EXPORT.json) to LEAN_PATH; never copy or move caches, never delete. Admission check before each scope (whole-host count < 6, disk ≥ 40 GB). Budget: 30 scopes. Record target, exit, wall, peak RSS, swap, revision and `#print axioms` per scope in NNT_COMPILE.tsv; raw-audit every delivered root (standard axioms only); write NNT_HANDOFF.md and NNT_REMAINING.md with before/after field statements. No Kani, extraction, Rust, SBF, push or ledger change. Report "target not yet established".
