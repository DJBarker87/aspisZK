import NNH8_Exec
import NNH_Run6Installed
import NPN_RecordedFrame
set_option autoImplicit false
noncomputable section
/-! NPN_ (Stream A, gate row 5 scoping job, 2026-11-10). Target not yet established.

The recorded world at the corrected host `NOC_Run5bHost.S_host`, with the
witness instantiation of every binder that is not the verifier's acceptance:

* `W := Heap (Nat → Record)`, `L0 := S2Trust.model`, `borrow := model_satisfies`,
  `copy := S2W_TrustedStd.specification`, `std := specification_satisfies`
  (the existing consistency witnesses of the two trust structures);
* `Tx := Bool` (TX1 = `false`, TX2 = `true`), `w := world r …` built from the
  recorded images by `NPN_RecordedFrame.obs`;
* `fx.a :=` the recorded pair as a zero-query adversary, `Q0 = Q1 = 0`. This is
  a witness instance; the theorems keep `a` universal and this module does not
  change them.

Proved here: Realizes-style field identities of the context, `QueriesF`, the
full host `GameFrame` (game (a)-(c), the non-trace part of (d), both
admissions and RuntimePersistence), and `Out2`. The remaining `Runs` fields
(`trace`, `ok1`, `out1`, `ok2`) are the evaluation residual, stated exactly
in `runs_of_residual`; they are NOT proved here. -/
namespace AspisR1.NPN_RecordedHost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
open NPN_RecordedFrame

abbrev W := Heap (Nat → Record)
abbrev L0 : Library W (Nat → Record) := S2Trust.model (Nat → Record)
abbrev copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record) :=
  S2W_TrustedStd.specification
theorem borrow : S2TrustedSdkBorrow L0 := S2Trust.model_satisfies _
theorem std : S2W_TrustedStd.TrustedStd copy := S2W_TrustedStd.specification_satisfies _

/-- The recorded pair as a zero-query two-phase adversary. -/
def adversary (r : Recorded) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    SCE_Experiment.Adversary Bool where
  first := .done ⟨e1 r, data1, true⟩
  second := fun _ _ _ _ => .done ⟨e2 r, data2, slot, true⟩

/-- Oracle-free data: `pda clock reservation indexError root length prior words D`
stay as supplied in `base`; only `a`, `Q0`, `Q1` are set. -/
def fixed (r : Recorded) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (base : NOC_Run5bCtx.Fixed) : NOC_Run5bCtx.Fixed :=
  { base with a := adversary r data1 data2 slot, Q0 := 0, Q1 := 0 }

def world (r : Recorded) (post1 post2 : Heap (Nat → Record)) : NOC_Run5bCtx.World W Bool :=
  ⟨(e1 r).heap, (e2 r).heap, r.saved, post1, post2, obs r, false, true, r.actions1⟩

abbrev S := NOC_Run5bHost.S_host (Tx := Bool) L0 copy std
abbrev X := NNH8_Exec.exec (Tx := Bool) L0 copy std

/-- The context of world `H` (condition (4): the pair is the adversary's output at `H`). -/
abbrev ctx (r : Recorded) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (base : NOC_Run5bCtx.Fixed) (post1 post2 : Heap (Nat → Record)) (H : Bytes → State) :=
  RSL.TASB.ctxB X (fixed r data1 data2 slot base) (world r post1 post2) H

theorem ctx_fields (r : Recorded) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (base : NOC_Run5bCtx.Fixed) (post1 post2 : Heap (Nat → Record)) (H : Bytes → State) :
    (ctx r data1 data2 slot base post1 post2 H).i = ⟨e1 r, data1, true⟩ ∧
    (ctx r data1 data2 slot base post1 post2 H).j = ⟨e2 r, data2, slot, true⟩ ∧
    (ctx r data1 data2 slot base post1 post2 H).world = world r post1 post2 ∧
    (ctx r data1 data2 slot base post1 post2 H).sha256 = H :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- L154 at the witness: the zero-query adversary issues nothing, for every
environment digest `J` and query oracle `K`. -/
theorem queries (r : Recorded) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (base : NOC_Run5bCtx.Fixed) :
    RSL.TASB.ExecB.QueriesF X (fixed r data1 data2 slot base) := by
  intro J K
  show List.length (ARW_Induced.issued _ _ _ _ (NNH_StateNormalize.normalize (adversary r data1 data2 slot)) K) ≤ 0 + 0
  unfold ARW_Induced.issued
  dsimp only
  split <;> simp [NNH_StateNormalize.normalize, NNH_StateNormalize.eval_map, adversary, eval]

/-- The full host GameFrame at the recorded world: game (a)-(c), the two
non-trace equalities of (d), and `NOC_Run5bHost.retained` (both admissions and
RuntimePersistence), from facts of the recording only. -/
theorem frame (r : Recorded) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (base : NOC_Run5bCtx.Fixed) (post1 post2 : Heap (Nat → Record)) (H : Bytes → State)
    (same : r.cell1 2 = r.cell2 6)
    (key : (r.meta1 (2 * r.cell1 2)).owned.key = (r.meta2 (2 * r.cell2 6)).owned.key)
    (inj1 : ∀ a b, a < 3 → b < 3 → keys (e1 r) a = keys (e1 r) b → r.cell1 a = r.cell1 b)
    (inj2 : ∀ a b, a < 7 → b < 7 → keys (e2 r) a = keys (e2 r) b → r.cell2 a = r.cell2 b) :
    S.GameFrame (ctx r data1 data2 slot base post1 post2 H) :=
  ⟨NPN_RecordedFrame.frame r same key, admission1 r inj1, admission2 r inj2,
    persistence r (Hist_Nonvacuity.key 0#u8)⟩

theorem out2 (r : Recorded) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (base : NOC_Run5bCtx.Fixed) (post1 post2 : Heap (Nat → Record)) (H : Bytes → State)
    (o : RSL.Obs (Except RSL.ProgramError Unit × RSL.SdkState)) :
    S.Out2 (ctx r data1 data2 slot base post1 post2 H) o := trivial

/-- The exact residual of gate row 5: given the recorded-frame facts, a `Runs`
inhabitant at the installed implementation needs exactly the trace association
and the two entry acceptances with TX1's carrier-image write events. -/
theorem runs_of_residual (allocation217 : RSL.Bytes → RSL.Env → Bool)
    (allocation234 : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
    (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation)
    (r : Recorded) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (base : NOC_Run5bCtx.Fixed) (post1 post2 : Heap (Nat → Record)) (H : Bytes → State)
    (same : r.cell1 2 = r.cell2 6)
    (key : (r.meta1 (2 * r.cell1 2)).owned.key = (r.meta2 (2 * r.cell2 6)).owned.key)
    (inj1 : ∀ a b, a < 3 → b < 3 → keys (e1 r) a = keys (e1 r) b → r.cell1 a = r.cell1 b)
    (inj2 : ∀ a b, a < 7 → b < 7 → keys (e2 r) a = keys (e2 r) b → r.cell2 a = r.cell2 b)
    (trace : S.TraceRep (ctx r data1 data2 slot base post1 post2 H)
      (NNH_Run6Installed.implementation allocation217 allocation234 ch
        NNG_Candidate344.allocation alloc2).entry)
    (ok1 : ∃ s', ((NNH_Run6Installed.implementation allocation217 allocation234 ch
        NNG_Candidate344.allocation alloc2).entry (S.args1 (ctx r data1 data2 slot base post1 post2 H))
        (S.state1 (ctx r data1 data2 slot base post1 post2 H))
        (S.env1 (ctx r data1 data2 slot base post1 post2 H))).exit = .ret (.ok (), s'))
    (out1 : S.Out1 (ctx r data1 data2 slot base post1 post2 H)
      ((NNH_Run6Installed.implementation allocation217 allocation234 ch
        NNG_Candidate344.allocation alloc2).entry (S.args1 (ctx r data1 data2 slot base post1 post2 H))
        (S.state1 (ctx r data1 data2 slot base post1 post2 H))
        (S.env1 (ctx r data1 data2 slot base post1 post2 H))))
    (ok2 : ∃ s', ((NNH_Run6Installed.implementation allocation217 allocation234 ch
        NNG_Candidate344.allocation alloc2).entry (S.args2 (ctx r data1 data2 slot base post1 post2 H))
        (S.state2 (ctx r data1 data2 slot base post1 post2 H))
        (S.env2 (ctx r data1 data2 slot base post1 post2 H))).exit = .ret (.ok (), s')) :
    RSL.TASB.Runs S (NNH_Run6Installed.implementation allocation217 allocation234 ch
      NNG_Candidate344.allocation alloc2) (ctx r data1 data2 slot base post1 post2 H) :=
  ⟨frame r data1 data2 slot base post1 post2 H same key inj1 inj2, trace, ok1, out1, ok2,
    out2 r data1 data2 slot base post1 post2 H _⟩

end AspisR1.NPN_RecordedHost
end
#print axioms AspisR1.NPN_RecordedHost.borrow
#print axioms AspisR1.NPN_RecordedHost.std
#print axioms AspisR1.NPN_RecordedHost.ctx_fields
#print axioms AspisR1.NPN_RecordedHost.queries
#print axioms AspisR1.NPN_RecordedHost.frame
#print axioms AspisR1.NPN_RecordedHost.out2
#print axioms AspisR1.NPN_RecordedHost.runs_of_residual
