import KNE_Leaf
import NCL_DriverForward
import DrvC_Installation
import Tx1Q_Control
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCT_DriverDomain
open Aeneas Aeneas.Std Result
open DrvC_Installation
open CheckpointBytes5Writer CheckpointBytes5Join CheckpointBytesBody CheckpointBytesBlocks

variable {F C : Type}

abbrev Cut (c : Configuration F C)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (saved : alloc.vec.Vec U8) :=
  NCL_DriverCuts.Cuts (currentInstalled c) (currentDigest c) semantic pub proof () saved

def writerPrepared (p : Tx1Q_Carriers.C.P) : Prepared :=
  CheckpointBytes3Namespaces.toPrepared (Tx1Q_Carriers.prepared p)

def writerAccumulator (out : Tx1Q_Carriers.C.A) (flushed : Slice Tx1Q_Carriers.C.K) : Accumulator :=
  CheckpointBytes3Namespaces.toAccumulator
    (Tx1Q_Carriers.accumulator {out with weights := ⟨flushed.val,flushed.property⟩})

/-- Accepted-cut model calls only. Completeness for all native reached calls,
including rejected/failing executions, is NOT part of this definition. -/
def Reached (c : Configuration F C) (p : Prepared) (a : Accumulator) : Prop :=
  ∃ semantic pub proof saved, ∃ cut : Cut c semantic pub proof saved,
    p = writerPrepared cut.prepared ∧ a = writerAccumulator cut.out cut.flushed

/-- NCL's inversion supplies the predicate witness on the same accepted call. -/
theorem of_accepted (c : Configuration F C)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (start : AspisR1CurrentCaller.compact.OFF_FOLDED_ROOT (currentInstalled c) = ok 7751#usize)
    (finish : AspisR1CurrentCaller.compact.OFF_ROUND1 (currentInstalled c) = ok 7783#usize)
    (returned : AspisR1CurrentCaller.verifier.candidate.tx1 (currentInstalled c)
      (currentDigest c) semantic pub proof split () none = ok (.Ok saved)) :
    ∃ cut : Cut c semantic pub proof saved,
      Reached c (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) := by
  obtain ⟨_,⟨cut⟩⟩ := NCL_DriverCuts.accepted _ _ semantic pub proof split () saved start finish returned
  exact ⟨cut,semantic,pub,proof,saved,cut,rfl,rfl⟩

/-- Conversely these cuts replay on the SAME inputs; no second acceptance premise. -/
theorem replay (c : Configuration F C)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (saved : alloc.vec.Vec U8)
    (start : AspisR1CurrentCaller.compact.OFF_FOLDED_ROOT (currentInstalled c) = ok 7751#usize)
    (finish : AspisR1CurrentCaller.compact.OFF_ROUND1 (currentInstalled c) = ok 7783#usize)
    (cut : Cut c semantic pub proof saved) :
    AspisR1CurrentCaller.verifier.candidate.tx1 (currentInstalled c) (currentDigest c)
      semantic pub proof 10#usize () none = ok (.Ok saved) :=
  NCL_DriverForward.source _ _ semantic pub proof () saved start finish cut

/-- Reuse the existing child-control proof on NCL's exact carriers. No parsing,
canonicality of prepared fields, or arithmetic primitive law is assumed here. -/
theorem control (c : Configuration F C)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (saved : alloc.vec.Vec U8)
    (cut : Cut c semantic pub proof saved) :
    (writerAccumulator cut.out cut.flushed).weights.val.length = 64 ∧
    (writerAccumulator cut.out cut.flushed).next.val = 10 ∧
    ∀ x ∈ (Tx1Q_Carriers.slice Tx1Q_Carriers.k cut.flushed).val,
      Port3_FlushInstall.Canonical x := by
  have init := Tx1Q_PrefixInstall.initial_success c.reserved cut.initial cut.initial_call
  have pend := Tx1Q_PrefixInstall.pending_success c.reserved cut.initial.weights.deref cut.pending cut.pending_call
  have geo := Tx1Q_PrefixInstall.geometry_success c.geometry cut.prepared.queries 0#usize 10#usize
    cut.geometry cut.geometry_call
  have qry := Tx1Q_Install.query_success (Tx1Q_QueryBridge.leaves c.query) proof cut.prepared
    cut.initial cut.out cut.scratch none cut.geometry cut.pending cut.after 10#usize cut.query
  rw [Tx1Q_QueryBridge.release_leaves] at qry
  have fl := Tx1Q_Install.flush_success cut.after cut.out.weights.deref cut.flushed cut.flush
  let run : Tx1Q_Execution.Run (currentInstalled c) c.reserved c.query c.geometry
      (currentDigest c) () semantic pub proof 10#usize saved :=
    { p := cut.prepared, zero := cut.zero, scratch := cut.scratch, initial := cut.initial,
      root := cut.root, geometry := cut.geometry, pending := cut.pending, out := cut.out,
      after := cut.after, flushed := cut.flushed, split_eq := rfl,
      prepare_call := cut.prepare, initial_call := init, batch_call := cut.batch,
      geometry_call := geo, pending_call := pend, query_call := qry,
      flush_call := fl, writer_call := cut.checkpoint }
  have h := Tx1Q_Control.fields _ _ _ _ _ _ _ _ _ _ _ run
  refine ⟨?_,h.2.2.1,h.2.2.2.2⟩
  simpa only [writerAccumulator,CheckpointBytes3Namespaces.toAccumulator,
    CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,
    List.length_map] using h.2.2.2.1

theorem reached_control (c : Configuration F C) (p : Prepared) (a : Accumulator)
    (reached : Reached c p a) : a.weights.val.length = 64 ∧ a.next.val = 10 := by
  obtain ⟨semantic,pub,proof,saved,cut,rfl,rfl⟩ := reached
  exact ⟨(control c semantic pub proof saved cut).1,(control c semantic pub proof saved cut).2.1⟩

/-- The weight part of CanonicalFields is genuinely discharged, on writer
carriers, rather than repeated as an external field gate. -/
theorem reached_weights (c : Configuration F C) (p : Prepared) (a : Accumulator)
    (h : Reached c p a) (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144) :
    ∀ j, OraclePortCkptAbi4Decode.Canonical
      ((fields p a (reached_control c p a h).1 qb).weights j) := by
  obtain ⟨semantic,pub,proof,saved,cut,rfl,rfl⟩ := h
  intro j
  have bound : j.val < cut.flushed.val.length := by
    have len := (control c semantic pub proof saved cut).1
    simp only [writerAccumulator,CheckpointBytes3Namespaces.toAccumulator,
      CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,
      List.length_map] at len
    rw [len]
    exact j.isLt
  have hc := (control c semantic pub proof saved cut).2.2
    (Tx1Q_Carriers.k (cut.flushed.val[j.val]))
    (List.mem_map.mpr ⟨cut.flushed.val[j.val],List.getElem_mem bound,rfl⟩)
  simpa only [fields,writerAccumulator,CheckpointBytes3Namespaces.toAccumulator,
    CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,
    List.getElem_map,CheckpointBytes3Namespaces.toK,Tx1Q_Carriers.k,
    OraclePortCkptAbi4Decode.Canonical,Port3_FlushInstall.Canonical] using hc

/-- EXACT remaining canonicality gates. The proved 64 weights are excluded.
This record is only organisation of the remaining assumptions, not discharge. -/
structure NonWeightCanonical (f : Fields) : Prop where
  gamma : OraclePortCkptAbi4Decode.CanonicalWide f.gamma
  kappa : OraclePortCkptAbi4Decode.CanonicalWide f.kappa
  alpha : ∀ j, OraclePortCkptAbi4Decode.CanonicalWide (f.alpha j)
  rho : OraclePortCkptAbi4Decode.Canonical f.rho
  semanticAlpha : ∀ j, OraclePortCkptAbi4Decode.Canonical (f.semanticAlpha j)
  coordinates : ∀ j, OraclePortCkptAbi4Decode.Canonical (f.coordinates j)
  claim : OraclePortCkptAbi4Decode.CanonicalWide f.claim
  rhs : OraclePortCkptAbi4Decode.CanonicalWide f.rhs
  power : OraclePortCkptAbi4Decode.Canonical f.power

/-- Strongest domain assembly with the missing field gates EXPLICIT. This is
conditional progress, not discharge of DriverEstablishedDomain from NCL alone. -/
theorem established (c : Configuration F C)
    (variant : ∀ p a, Reached c p a → p.variant = .S2)
    (queries : ∀ p a, Reached c p a → ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : ∀ p a (h : Reached c p a),
      NonWeightCanonical (fields p a (reached_control c p a h).1 (queries p a h))) :
    KNE_Caller.DriverEstablishedDomain (Reached c) := by
  intro p a h
  have sizes := reached_control c p a h
  have old := canonical p a h
  have full : CanonicalFields (fields p a sizes.1 (queries p a h)) :=
    ⟨old.gamma,old.kappa,old.alpha,old.rho,old.semanticAlpha,old.coordinates,
      old.claim,old.rhs,old.power,reached_weights c p a h (queries p a h)⟩
  exact ⟨prepared (fields p a sizes.1 (queries p a h)) full,
    accumulator (fields p a sizes.1 (queries p a h)) full,
    variant p a h,sizes.1,queries p a h,full,sizes.2,rfl,rfl⟩

/-- Pointwise form: the same explicit remaining gates, with no universal
DriverEstablishedDomain or independently supplied WriterDomain premise. -/
theorem on_call (c : Configuration F C) (p : Prepared) (a : Accumulator)
    (h : Reached c p a) (variant : p.variant = .S2)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : NonWeightCanonical (fields p a (reached_control c p a h).1 qb)) :
    KNE_Caller.WriterDomain p a :=
  ⟨variant,(reached_control c p a h).1,qb,
    ⟨canonical.gamma,canonical.kappa,canonical.alpha,canonical.rho,
      canonical.semanticAlpha,canonical.coordinates,canonical.claim,canonical.rhs,
      canonical.power,reached_weights c p a h qb⟩,(reached_control c p a h).2⟩

section Leaf
variable (c : Configuration F C)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public1 proof : Slice U8) (saved : alloc.vec.Vec U8)
    (cut : Cut c semantic public1 proof saved)

theorem cutReached : Reached c (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) := ⟨semantic,public1,proof,saved,cut,rfl,rfl⟩


theorem callDomain
    (variant : ((writerPrepared cut.prepared)).variant = .S2)
    (qb : ∀ j : Fin 22,
      (((writerPrepared cut.prepared)).queries.val[j.val]'(by simpa [((writerPrepared cut.prepared)).queries.property] using j.isLt)).val < 262144)
    (canonical : NonWeightCanonical (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed)
      (reached_control c (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (cutReached c semantic public1 proof saved cut)).1 qb)) :
    KNE_Caller.WriterDomain (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) :=
  on_call c (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (cutReached c semantic public1 proof saved cut) variant qb canonical


/-- Step-4 fallback: SAME model-driver proof/public and writer p/a. The three
unproved input-field gates remain explicit. This is NOT an unconditional
model driver theorem and is NOT a native driver call association. -/

theorem native_result
    (variant : ((writerPrepared cut.prepared)).variant = .S2)
    (qb : ∀ j : Fin 22,
      (((writerPrepared cut.prepared)).queries.val[j.val]'(by simpa [((writerPrepared cut.prepared)).queries.property] using j.isLt)).val < 262144)
    (canonical : NonWeightCanonical (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed)
      (reached_control c (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (cutReached c semantic public1 proof saved cut)).1 qb))
    (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () H)
    (native : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.DuplexFrames.Bytes →
      AspisV8R19.DuplexFrames.Bytes → Prop)
    (valid : KNE_Composition.LocalCorrect native KND_Schedule.schedule)
    (hp hu hc : CheckpointBytes5Effect.Digest) (body out : Slice U8)
    (before : CheckpointBytes5Effect.Log)
    (tr : KNE_Composition.Trace native (KNE_Model.bodyEmissions
      (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) ((callDomain c semantic public1 proof saved cut variant qb canonical)).size ((callDomain c semantic public1 proof saved cut variant qb canonical)).queriesBound)
      (CheckpointBytesDigest.stateOf hp) (CheckpointBytesDigest.stateOf hu)) []
      (MultiproofConeCanonical.bytesOf body.val))
    (checksumWrite : native (MultiproofConeCanonical.bytesOf body.val)
      (MultiproofConeCanonical.bytesOf hc.val) (MultiproofConeCanonical.bytesOf out.val))
    (proofCall : ((VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c)))).digest () (AspisR1Stage2.WireTx2.singletonParts proof) = ok hp)
    (publicCall : ((VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c)))).digest () (AspisR1Stage2.WireTx2.singletonParts public1) = ok hu)
    (checksumCall : ((VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c)))).digest () (AspisR1Stage2.WireTx2.checksumParts body) = ok hc) :
    KNE_Schedule.sourceFinalLen ((writerPrepared cut.prepared)).variant = 64 ∧
    out.val = saved.val ∧
    out.val.length = 1768 ∧
    out = LPm_CheckpointProgram.returned (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) ((callDomain c semantic public1 proof saved cut variant qb canonical)).size ((callDomain c semantic public1 proof saved cut variant qb canonical)).queriesBound
      ((callDomain c semantic public1 proof saved cut variant qb canonical)).canonical ((callDomain c semantic public1 proof saved cut variant qb canonical)).next hp hu hc ∧
    CheckpointBytes5Effect.run (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () (writer (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) proof public1) before =
      ok (out,((before ++ [(AspisR1Stage2.WireTx2.singletonParts proof,hp)]) ++
        [(AspisR1Stage2.WireTx2.singletonParts public1,hu)]) ++
        [(AspisR1Stage2.WireTx2.checksumParts body,hc)]) ∧
    MultiproofConeCanonical.bytesOf out.val = OraclePortCheckpointAbiC5.encode H
      (MultiproofConeCanonical.bytesOf proof.val) (MultiproofConeCanonical.bytesOf public1.val)
      (prepared (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) ((callDomain c semantic public1 proof saved cut variant qb canonical)).size ((callDomain c semantic public1 proof saved cut variant qb canonical)).queriesBound) ((callDomain c semantic public1 proof saved cut variant qb canonical)).canonical)
      (accumulator (fields (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) ((callDomain c semantic public1 proof saved cut variant qb canonical)).size ((callDomain c semantic public1 proof saved cut variant qb canonical)).queriesBound) ((callDomain c semantic public1 proof saved cut variant qb canonical)).canonical) := by
  have leaf := KNE_Leaf.native_result (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () H oracle native valid (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (callDomain c semantic public1 proof saved cut variant qb canonical) proof public1
    hp hu hc body out before tr checksumWrite proofCall publicCall checksumCall
  obtain ⟨after,modelRun⟩ := Port3_CheckpointInstall.writer_run
    (Tx1Q_Install.digest (currentDigest c)) (Tx1Q_Carriers.prepared cut.prepared)
    (Tx1Q_Carriers.accumulator {cut.out with weights := ⟨cut.flushed.val,cut.flushed.property⟩})
    proof public1 () saved cut.checkpoint before
  have same : VTop_Checkpoint.checkpointSlice saved = out :=
    congrArg Prod.fst (Result.ok.inj (modelRun.symm.trans leaf.2.2.1))
  exact ⟨KNE_Schedule.caller_final_len (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) (callDomain c semantic public1 proof saved cut variant qb canonical),congrArg Subtype.val same.symm,leaf⟩
end Leaf

#print axioms of_accepted
#print axioms replay
#print axioms control
#print axioms reached_control
#print axioms reached_weights
#print axioms established
#print axioms on_call
#print axioms cutReached
#print axioms callDomain
#print axioms native_result
end AspisR1.NCT_DriverDomain
end
