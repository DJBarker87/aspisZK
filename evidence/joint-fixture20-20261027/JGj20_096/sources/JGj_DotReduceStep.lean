import JGj_DotReducer
import JGj_DotWordStep
import JGj_RawBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_DotReduceStep
open Aeneas Aeneas.Std Result WP FIq_Native
open JGj_RawBounds
open FJb_TailCell (cell)
def step (sums raw : Raw) (i : Usize) : Result Raw := do
  let x ← Array.index_usize raw i
  let m ← field.M31.reduce_u64 x
  let y ← Array.index_usize sums i
  let z ← y+UScalar.cast .U64 m
  Array.update sums i z
theorem source (sums raw : Raw) (i : Usize) (n : Nat)
    (hi : i.val<(4#usize).val) (hn : n≤10) (hs : Bound sums (n*P)) :
    ∃ out,step sums raw i=ok out ∧ Bound out ((n+1)*P) := by
  let x := cell raw ⟨i.val,hi⟩
  let y := cell sums ⟨i.val,hi⟩
  have rx : Array.index_usize raw i=ok x := RawPoseidonExternalRowReads.array_index_usize_ok raw i hi
  have ry : Array.index_usize sums i=ok y := RawPoseidonExternalRowReads.array_index_usize_ok sums i hi
  obtain ⟨m,rm,cm⟩ := JGj_DotReducer.source x
  have cm' : m.val<P := cm
  have by0 : y.val<n*P := hs _
  have prod : n*P≤10*P := Nat.mul_le_mul_right P hn
  have lim : 11*P<2^64 := by norm_num [P,AspisV8R17.RawReducer.P]
  have cast : (UScalar.cast .U64 m).val=m.val := JGj_DotWordStep.wide_value m
  obtain ⟨z,rz,vz⟩ := ExtractedMaskReducerOps.add_success y (UScalar.cast .U64 m) (by rw [cast];omega)
  have rzNative : (y+UScalar.cast .U64 m : Result U64)=ok z := rz
  have bz : z.val<(n+1)*P := by rw [vz,cast,Nat.add_mul,Nat.one_mul];omega
  have ba : Bound sums ((n+1)*P) := by
    intro j
    have h := hs j
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
  obtain ⟨out,ro,vo⟩ := WP.spec_imp_exists (Array.update_spec sums i z (by simpa only [sums.property] using hi))
  exact ⟨out,by simp only [step,rx,rm,ry,rzNative,ro,bind_tc_ok],vo ▸ JGj_RawBounds.update _ _ i z hi ba bz⟩
#print axioms source
end AspisR1.JGj_DotReduceStep
end
