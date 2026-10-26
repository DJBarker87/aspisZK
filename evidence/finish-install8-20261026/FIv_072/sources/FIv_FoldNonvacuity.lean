import FIv_FoldsTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_FoldNonvacuity
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
abbrev zero : NQ := FIq_Native.field.QM31.ZERO
def semantic : Array NQ 24#usize := ⟨List.replicate 24 zero,by simp only [List.length_replicate];rfl⟩
def poseidon : Array NQ 4#usize := ⟨List.replicate 4 zero,by simp only [List.length_replicate];rfl⟩
theorem value : ∃ out, FIv_FoldsTotal.body semantic poseidon zero zero=ok out ∧
    Canon out ∧ decode out=0 := by
  have hs : ∀ x∈semantic.val,Canon x := by
    intro x hx
    rcases List.mem_replicate.mp hx with ⟨_,rfl⟩
    exact FIv_NativeValue.zero.1
  have hp : ∀ x∈poseidon.val,Canon x := by
    intro x hx
    rcases List.mem_replicate.mp hx with ⟨_,rfl⟩
    exact FIv_NativeValue.zero.1
  obtain ⟨out,run,hc,hv⟩ := FIv_FoldsTotal.value semantic poseidon zero zero
    FIv_NativeValue.zero.1 FIv_NativeValue.zero.1 hs hp
  have low : FIv_HornerAlgebra.low 0 poseidon.val=0 := by
    change decode zero+0*FIv_HornerAlgebra.low 0 (List.replicate 3 zero)=0
    rw [FIv_NativeValue.zero.2]
    ring
  have dz : decode zero=0 := FIv_NativeValue.zero.2
  have polynomial : FIv_CompositionValue.polynomial (decode zero) semantic poseidon zero=0 := by
    change decode zero^28*decode zero+decode zero^4*FIv_HornerAlgebra.low (decode zero) semantic.val+
      FIv_HornerAlgebra.low (decode zero) poseidon.val=0
    rw [dz,zero_pow (by decide : (28:Nat)≠0),zero_pow (by decide : (4:Nat)≠0)]
    simpa only [zero_mul,zero_add] using low
  exact ⟨out,run,hc,hv.trans polynomial⟩

#print axioms value
end AspisR1.FIv_FoldNonvacuity
end
