import PFin_RunLevelBound
import SdkC_Replay
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_ReplayBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortFrozenOrder PFin_AddressBound
attribute [local instance] Classical.propDecidable

theorem inPlace (root : State) (live : Live) (nodes : Bytes) : Bounded (verifyInPlace root live nodes) := by
  unfold verifyInPlace
  split_ifs
  · exact PFin_AddressBound.bind _ _ (PFin_RunLevelBound.levels _ _ _) (fun _=>done _)
  · exact done _

theorem tail (p : Parsed) (batch kind : Nat) (live : Live) : Bounded (slotTail p batch kind live) := by
  unfold slotTail
  split_ifs <;> first | exact done _ | exact inPlace _ _ _

theorem slot (p : Parsed) (q : Fin 22 → Fin 262144) (batch kind : Nat) :
    Bounded (verifySlot_frozen p q batch kind) := by
  apply PFin_AddressBound.bind _ _ (PFin_HashLeavesBound.leaves _ _ _ _ _)
  intro result
  cases result with
  | none => exact done _
  | some live => exact tail p batch kind live

theorem short (ps : List (Program Bytes State Bool)) (bound : ∀ p∈ps,Bounded p) :
    Bounded (OraclePortShortCircuit.short ps) := by
  induction ps with
  | nil => exact done _
  | cons p rest ih =>
    apply PFin_AddressBound.bind _ _ (bound p (List.mem_cons_self ..))
    intro accepted
    cases accepted with
    | false => exact done _
    | true => exact ih (fun x member=>bound x (List.mem_cons_of_mem _ member))

theorem batch (p : Parsed) (q : Fin 22 → Fin 262144) (ss : List (Nat × Nat)) :
    Bounded (OraclePortFrozen2.batch p q ss) := by
  apply short
  intro program member
  obtain ⟨s,_,same⟩ := List.mem_map.mp member
  subst program
  exact slot p q s.1 s.2

theorem replay (p : Parsed) (q : Fin 22 → Fin 262144) : Bounded (SdkC_Replay.replay p q) :=
  batch p q _

#print axioms inPlace
#print axioms tail
#print axioms slot
#print axioms short
#print axioms batch
#print axioms replay
end AspisR1.PFin_ReplayBound
end
