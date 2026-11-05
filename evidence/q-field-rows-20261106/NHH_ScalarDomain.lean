import NHH_BaseOps
import NFG_NormFold
set_option autoImplicit false
noncomputable section
namespace NHH_ScalarDomain
open Aeneas Aeneas.Std Result AspisR1

theorem add_probe (x y : U32) :
 NFG_InverseRef.field.M31.add x y=AspisR1Qm31ArithmeticProbe.field.M31.add x y := by
 simp only [NFG_InverseRef.field.M31.add,AspisR1Qm31ArithmeticProbe.field.M31.add,
 NFG_InverseRef.field.P,AspisR1Qm31ArithmeticProbe.field.P]

theorem addition (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
 ∃ out, NFG_InverseRef.field.M31.add x y=ok out ∧
 out.val=(x.val+y.val)%2147483647 ∧ out.val<2147483647 := by
 simpa only [add_probe] using ExtractedCurrentM31AddSub.current_add_mod x y hx hy

theorem inverse_probe (x : U32) :
 NFG_InverseRef.field.M31.inv x=SAQ_Inverse.source x :=
 (NHH_BaseOps.inverse_chain x).trans (congrFun SAQ_Inverse.source_eq_reference x).symm

theorem inverse_total (x : U32) (hx : x != 0#u32) :
 ∃ out, NFG_InverseRef.field.M31.inv x=ok out ∧ out.val<2147483647 := by
 obtain ⟨out,ho,_⟩ := AspisR1M31Inverse.SquareProof.current_inv_total_power x hx
 exact ⟨out,(inverse_probe x).trans ho,
 AspisR1M31Inverse.SquareProof.current_inv_success_canonical x out ho⟩

theorem inverse_zero : NFG_InverseRef.field.M31.inv 0#u32=fail .assertionFailure := by
 simp [NFG_InverseRef.field.M31.inv,massert]

/-- Derive the backend's canonical nonzero input from the SAME two products. -/
theorem norm (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647)
 (live : ¬(a=0#u32 ∧ b=0#u32)) :
 ∃ aa bb n,
 NFG_InverseRef.field.M31.mul a a=ok aa ∧ aa.val<2147483647 ∧
 NFG_InverseRef.field.M31.mul b b=ok bb ∧ bb.val<2147483647 ∧
 NFG_InverseRef.field.M31.add aa bb=ok n ∧ n.val<2147483647 ∧ n != 0#u32 := by
 obtain ⟨aa,haa,vaa,caa⟩ := NHH_BaseOps.mul_value a a
 obtain ⟨bb,hbb,vbb,cbb⟩ := NHH_BaseOps.mul_value b b
 obtain ⟨n,hn,vn,cn⟩ := addition aa bb caa cbb
 have liveNat : ¬(a.val=0 ∧ b.val=0) := by
  intro h;apply live;exact ⟨UScalar.eq_of_val_eq h.1,UScalar.eq_of_val_eq h.2⟩
 have same : n.val=((a.val*a.val)%2147483647+(b.val*b.val)%2147483647)%2147483647 := by
  simpa only [vaa,vbb] using vn
 have nonzero := (NFG_NormFold.backend_domain a.val b.val n.val ha hb liveNat same).2
 have nz : n != 0#u32 := by
  simp only [bne_iff_ne]
  intro h;exact nonzero (congrArg UScalar.val h)
 exact ⟨aa,bb,n,haa,caa,hbb,cbb,hn,cn,nz⟩

#print axioms add_probe
#print axioms addition
#print axioms inverse_probe
#print axioms inverse_total
#print axioms inverse_zero
#print axioms norm
end NHH_ScalarDomain
end
