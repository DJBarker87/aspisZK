import RPu_FJf_InstalledPointCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_QMArray
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ qm)

def canon {N : Usize} (a : Array NQ N) : Prop := ∀ x∈a.val,FIo_QMValues.Canon x

def value {N : Usize} (a : Array NQ N) (j : Nat) : OraclePortCheckpointAbiC5.K :=
  match a.val[j]? with | some x => decodeQM (qm x) | none => 0

theorem read {N : Usize} (a : Array NQ N) (i : Usize) (x : NQ)
    (run : Array.index_usize a i=ok x) : value a i.val=decodeQM (qm x) := by
  simp only [value,FJc_ReadSlot.slot _ _ _ run]

theorem update {N : Usize} (a b : Array NQ N) (i : Usize) (x : NQ)
    (run : Array.update a i x=ok b) (j : Nat) :
    value b j=if i.val=j then decodeQM (qm x) else value a j := by
  unfold value
  rw [FJf_ArraySlots.update_slot a b i x run j]
  by_cases h : i.val=j
  · simp only [if_pos h]
  · simp only [if_neg h]

theorem update_canon {N : Usize} (a b : Array NQ N) (i : Usize) (x : NQ)
    (ha : canon a) (hx : FIo_QMValues.Canon x) (run : Array.update a i x=ok b) : canon b := by
  unfold canon
  rw [FJf_ArrayOps.update_val a b i x run]
  exact FIo_ArrayCanon.list_set FIo_QMValues.Canon _ _ x ha hx

theorem zeros (N : Usize) : canon (Array.repeat N FIo_Native.aspis_core.field.QM31.ZERO) := by
  intro x hx
  simp only [Array.repeat,List.mem_replicate] at hx
  rcases hx with ⟨_,rfl⟩
  simp [FIo_QMValues.Canon,FIo_CMValues.Canon,FIo_Native.aspis_core.field.QM31.ZERO]
#print axioms read
#print axioms update
#print axioms update_canon
#print axioms zeros
end AspisR1.FJf_QMArray
end
