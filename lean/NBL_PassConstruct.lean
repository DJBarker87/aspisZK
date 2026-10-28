import LPk_Induction
set_option autoImplicit false
namespace AspisR1.NBL_PassConstruct
open SamplerMachineBounds SamplerWord SamplerWordPass SamplerRepeatedPass

theorem pass (r : UInt64) (xs : List UInt32) (good : r.toNat<P) :
    ∃ out qs, LPk_Induction.Pass r xs out qs := by
  induction xs generalizing r with
  | nil => exact ⟨r,[],.nil r⟩
  | cons d ds ih =>
    let step := machineStep r d
    let r1 := UInt64.ofNat step.2.toNat
    have r1value : r1.toNat=step.2.toNat := uint32_to_uint64_toNat step.2
    have relation := LPk_Step.machine_step r d good
    have bounded : r1.toNat<P := by rw [r1value];exact relation.2
    obtain ⟨out,qs,tail⟩ := ih r1 bounded
    refine ⟨out,step.1::qs,.cons ?_ tail⟩
    simpa only [r1value] using relation

theorem digits (n : Nat) (xs : List UInt32) :
    ∃ ds out, LPk_Induction.Digits n xs ds out := by
  induction n generalizing xs with
  | zero => exact ⟨[],xs,.nil xs⟩
  | succ n ih =>
    obtain ⟨r,qs,first⟩ := pass 0 xs P_pos
    obtain ⟨ds,out,tail⟩ := ih qs
    exact ⟨r.toNat::ds,out,.cons first tail⟩

theorem pass_length {r out : UInt64} {xs qs : List UInt32}
    (trace : LPk_Induction.Pass r xs out qs) : qs.length=xs.length := by
  induction trace with
  | nil => rfl
  | cons step tail ih => simpa only [List.length_cons] using congrArg Nat.succ ih

theorem digits_length {n : Nat} {xs out : List UInt32} {ds : List Nat}
    (trace : LPk_Induction.Digits n xs ds out) : ds.length=n ∧ out.length=xs.length := by
  induction trace with
  | nil => exact ⟨rfl,rfl⟩
  | cons first tail ih =>
    exact ⟨congrArg Nat.succ ih.1,ih.2.trans (pass_length first)⟩

#print axioms pass
#print axioms digits
#print axioms pass_length
#print axioms digits_length
end AspisR1.NBL_PassConstruct
