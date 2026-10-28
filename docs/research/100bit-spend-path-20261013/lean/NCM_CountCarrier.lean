import NCE_CountFullCuts
import NCE_VerifierAdmission

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_CountCarrier
open Aeneas Aeneas.Std NCE_OpeningCuts NCE_CountCuts NCE_CountInitCuts
open NCE_CountRowCuts NCE_CountLevelCuts
open MultiproofConeCountPhysical MultiproofConePhysicalViews
attribute [local instance] Classical.propDecidable

structure Ops where
  create : (Nat → Nat) → Nat → Carrier → InitState Carrier
  copy : InitState Carrier → InitState Carrier
  scan : ScanState (Nat × Carrier) → Bool × ScanState (Nat × Carrier)
  store : RowState (Nat × Carrier) → Nat → RowState (Nat × Carrier)
  height : RowState (Nat × Carrier) → LevelState Carrier

def compute (ops : Ops) (s : Carrier) : Nat × Carrier :=
  let initialized := NCE_CountInitCuts.run ops.copy s.scratch.n.val
    (ops.create (NCE_AdmissionCuts.index s) s.scratch.n.val s)
  let out := NCE_CountFullCuts.levels ops.scan ops.store ops.height 18
    ⟨initialized.memory,initialized.n,0,0,initialized.frame⟩
  (out.count,out.frame)

def count (ops : Ops) (pair range : NCE_AdmissionCuts.Predicate) (s : Carrier) : Option (Nat × Carrier) :=
  if s.scratch.n.val > 16 then none else
    let checked := NCE_AdmissionCuts.check pair range s
    if checked.1 then some (compute ops checked.2) else none

/-- Admission is computed from local predicates before count initialization.
The actual initialized private array feeds all eighteen levels; its frame is
THAT same full caller, including the old chronological log. -/
theorem valid (ops : Ops)
    (zero : NCE_Native_CountZero ops.create) (copy : NCE_Native_CountCopy ops.copy)
    (scan : NCE_Native_CountScan ops.scan) (store : NCE_Native_CountCommit ops.store)
    (height : NCE_Native_CountHeight ops.height)
    (s : Carrier)
    (well : OraclePortFrozenOrder.wellFormed ((live s.scratch 0 s.scratch.n.val).map Prod.fst)) :
    compute ops s = (MultiproofConeSlotTail.slotCount s.scratch,s) := by
  have keys := NCE_VerifierAdmission.same_indices s
  have length : (cells (NCE_AdmissionCuts.index s) 0 s.scratch.n.val).length = s.scratch.n.val := by
    simp only [cells,List.length_map,List.length_range]
  have wf : OraclePortFrozenOrder.wellFormed (cells (NCE_AdmissionCuts.index s) 0 s.scratch.n.val) := by
    rw [keys]
    exact well
  have small : s.scratch.n.val ≤ 16 := by have := wf.2.1;omega
  have order := wf.2.2.1
  have range : ∀ k, k < s.scratch.n.val → NCE_AdmissionCuts.index s k < 262144 := by
    intro k kb
    have mem : NCE_AdmissionCuts.index s k ∈ cells (NCE_AdmissionCuts.index s) 0 s.scratch.n.val := by
      simp only [cells]
      exact List.mem_map.mpr ⟨k,List.mem_range.mpr kb,by simp⟩
    exact wf.2.2.2 _ mem
  have result := NCE_CountFullCuts.initialized_eighteen ops.create zero ops.copy copy ops.scan scan ops.store store ops.height height
    (NCE_AdmissionCuts.index s) s.scratch.n.val s small order range
  apply Prod.ext
  · exact result.1.trans ((MultiproofConeCountLevels.count_eq 18 _ order).trans
      (by rw [keys,MultiproofConeSlotTail.slot_count_eq]))
  · exact result.2

#print axioms valid
end AspisR1.NCM_CountCarrier
end
