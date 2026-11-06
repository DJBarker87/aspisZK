import NJP_CohortTotal

set_option autoImplicit false
noncomputable section
namespace NJV_VerifierView
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite NJP_CohortRowLoop
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.MultiproofConePhysicalTransport AspisR1.MultiproofConePhysicalViews
open AspisR1.OraclePortFrozenOrder

/-- Full returning view of the adopted cohort. Native entry-condition transport
and the unit-domain caller clauses remain separate obligations. -/
theorem returning (H : Bytes → State) (root : RefDigest) (physical : Slice U8)
    (s : reference.Scratch) (zero : s.«at»=0#usize)
    (domain : AspisR1.MultiproofConeLevelIteration.Domain physical s)
    (bytes : physical.val.length ≤ 9216)
    (guard : wellFormed ((live s 0 s.n.val).map Prod.fst) ∧ physical.val.length%32=0) :
 eval H (transport (NJP_CohortReturning.run root physical s))=
 ((eval H (AspisR1.MultiproofConeVerifyState.verifyState root physical s)).1,
  ok (eval H (AspisR1.MultiproofConeVerifyState.verifyState root physical s)).2) := by
 obtain ⟨out,returned⟩ := NJP_CohortTotal.levels (rawOracle H) 18 physical s domain bytes
 have initial : {s with «at»:=0#usize}=s := by
   rw [←zero]
 unfold NJP_CohortReturning.run AspisR1.MultiproofConeVerifyState.verifyState
 rw [initial,if_pos guard]
 simp only [transport_observation,AspisR1.MultiproofConePhysicalLevels.bindRun,eval_bind,
   returned,AspisR1.MultiproofConePhysicalProgram.checked,eval,List.append_nil]
 cases out <;> rfl

#print returning
#print axioms returning
end NJV_VerifierView
end
