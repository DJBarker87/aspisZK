import PV_L1D_SelectedCount
import PV_L1D_RejectionCount
set_option autoImplicit false
namespace PV_L1D_UploadCounts
open R1Z.SideChannelL1AttemptRecord
open R1Z.ProverCommitRetry34 (Published)
/-- Mathematical quotient/remainder value of usize::div_ceil(3763).
It consumes the same published proof length, not an independently sampled size.
Allocation, upload requests and delivery prefixes require their native laws. -/
def uploads (n : Nat) : Nat := n/3763 + if n%3763=0 then 0 else 1

theorem ceil_formula (n : Nat) : uploads n = (n+3762)/3763 := by
  unfold uploads
  split <;> omega
#print axioms ceil_formula

variable {S Audit A : Type}
abbrev Proof (Audit : Type) := List UInt8 × Audit
/-- Same original state, owner, result and proof bytes throughout. This is a
model value law; it does not assert a joint native honest-run simulation. -/
theorem same_original_result (owner : Owner S (Proof Audit)) (s : S)
    (p : Published (Proof Audit)) (keys : Fin 8 → A)
    (h : (run owner 8 0 s).1.result = .done p) :
    ∃ k : Fin 8, k.val=p.attempts-1 ∧
      PV_L1D_SelectedCount.selected keys p.attempts (run owner 8 0 s).1.attempts.length =
        some (k.val,keys k) ∧
      ((run owner 8 0 s).1.attempts.length,
        ((run owner 8 0 s).1.attempts.filter PV_L1D_RejectionCount.retrying).length,
        uploads p.proof.1.length, (1 : Nat)) =
      (p.attempts,p.attempts-1,(p.proof.1.length+3762)/3763,1) := by
  obtain ⟨k,hk,selected⟩ := PV_L1D_SelectedCount.original_success owner s p keys h
  refine ⟨k,hk,selected,?_⟩
  have hc := PV_L1D_CountSuccess.count_eq_entered owner 8 0 s p h
  have hr := PV_L1D_RejectionCount.success_rejections owner 8 0 s p h
  have entered : (run owner 8 0 s).1.attempts.length = p.attempts := by omega
  have rejected : ((run owner 8 0 s).1.attempts.filter PV_L1D_RejectionCount.retrying).length = p.attempts-1 := by omega
  rw [entered,rejected,ceil_formula]
#print axioms same_original_result
end PV_L1D_UploadCounts
