import NJV_VerifierView
import NJP_AbortTransport
import NJE_WellPacket

set_option autoImplicit false
noncomputable section
namespace NJV_Entry
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite NJP_CohortRowLoop
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.MultiproofConePhysicalTransport AspisR1.MultiproofConePhysicalViews
open AspisR1.OraclePortFrozenOrder
attribute [local instance] Classical.propDecidable

/-- Actual binary entry guard, before the local cursor is reset. NJP_K064/065
certify the scalar short-circuit; NJE_WellPacket supplies the SAME slice reply. -/
def Guard (physical : Slice U8) (s : reference.Scratch) : Prop :=
 wellFormed ((live s 0 s.n.val).map Prod.fst) ∧ physical.val.length%32=0

def program (root : RefDigest) (physical : Slice U8) (s : reference.Scratch) :=
 if Guard physical s then NJP_CohortReturning.run root physical s
 else .done (ok (false,s))

def rawProgram (root : RefDigest) (physical : Slice U8) (s : reference.Scratch) :=
 if Guard physical s then
   NJP_LoopModel.run (decode root) (fun n => physical.val[n]!) physical.val.length (raw s)
 else .done (ok (false,raw s))

theorem guard_domain (physical : Slice U8) (s : reference.Scratch)
    (guard : Guard physical s) :
    0<s.n.val ∧ s.n.val≤16 := by
 have len : ((live s 0 s.n.val).map Prod.fst).length=s.n.val := by
   simp [AspisR1.MultiproofConeRootGuard.live_length]
 constructor
 · by_contra bad
   have empty : (live s 0 s.n.val).map Prod.fst=[] := List.length_eq_zero_iff.mp (by omega)
   exact guard.1.1 empty
 · have small := guard.1.2.1
   omega

/-- Complete returning Result, both buffers and cursor; early rejection keeps
all scratch and emits no query. No successful-verification premise. -/
theorem observation (H : Slice (Slice U8) → RefDigest) (root : RefDigest)
    (physical : Slice U8) (s : reference.Scratch) :
 let typed := eval H (program root physical s)
 (typed.1,mapResult NJP_CohortReturning.answer typed.2)=
 eval H (NJP_RequestTransport.transport (rawProgram root physical s)) := by
 dsimp only
 by_cases guard : Guard physical s
 · have d := guard_domain physical s guard
   simp only [program,rawProgram,if_pos guard]
   exact NJP_CohortReturning.observation H root physical s d.1 d.2
 · simp only [program,rawProgram,if_neg guard,NJP_RequestTransport.transport,eval,
     mapResult,NJP_CohortReturning.answer]

/-- Adopted full-state endpoint, including rejected buffers. Initial zero is
ABI bookkeeping, not an output or successful-child equation. -/
theorem adopted (H : Bytes → State) (root : RefDigest) (physical : Slice U8)
    (s : reference.Scratch) (zero : s.«at»=0#usize) (bytes : physical.val.length≤9216) :
 eval H (transport (program root physical s))=
 ((eval H (AspisR1.MultiproofConeVerifyState.verifyState root physical s)).1,
  ok (eval H (AspisR1.MultiproofConeVerifyState.verifyState root physical s)).2) := by
 by_cases guard : Guard physical s
 · have d := guard_domain physical s guard
   have domain : AspisR1.MultiproofConeLevelIteration.Domain physical s :=
     ⟨d.1,d.2,by rw [zero];simp⟩
   simp only [program,if_pos guard]
   exact NJV_VerifierView.returning H root physical s zero domain bytes guard
 · simp only [program,if_neg guard,transport,eval,
     AspisR1.MultiproofConeVerifyState.verifyState,Guard] at *
   rw [if_neg guard]
   rfl

#print guard_domain
#print axioms guard_domain
#print observation
#print axioms observation
#print adopted
#print axioms adopted
end NJV_Entry
end
