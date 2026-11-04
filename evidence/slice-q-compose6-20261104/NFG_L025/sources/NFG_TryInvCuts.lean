import NFG_InverseRef.Funs
import NFG_ResultCongr
set_option autoImplicit false
namespace NFG_TryInvCuts
open Aeneas Aeneas.Std Result NFG_InverseRef
/-- No square or inverse observation is independently chosen. -/
theorem accepted (x out : field.QM31) (run : field.QM31.try_inv x=ok (some out)) :
 field.QM31.is_zero x=ok false ∧
 ∃ aa bb rotated norm inverse real negative imag : field.CM31,
 field.CM31.square x.c0=ok aa ∧ field.CM31.square x.c1=ok bb ∧
 field.mul_by_r bb=ok rotated ∧ field.CM31.sub aa rotated=ok norm ∧
 field.CM31.inv norm=ok inverse ∧ field.CM31.mul x.c0 inverse=ok real ∧
 field.CM31.neg x.c1=ok negative ∧ field.CM31.mul negative inverse=ok imag ∧
 out=⟨real,imag⟩ := by
 unfold field.QM31.try_inv at run
 obtain ⟨test,ht,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 cases test with
 | true => cases run
 | false =>
  obtain ⟨aa,ha,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨bb,hb,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨rotated,hr,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨norm,hn,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨inverse,hi,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨real,hv,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨negative,hg,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  obtain ⟨imag,hm,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
  have same := Option.some.inj (Result.ok.inj run)
  exact ⟨ht,aa,bb,rotated,norm,inverse,real,negative,imag,ha,hb,hr,hn,hi,hv,hg,hm,same.symm⟩

theorem zero (x : field.QM31) (test : field.QM31.is_zero x=ok true) :
 field.QM31.try_inv x=ok none := by
 simp only [field.QM31.try_inv,test,bind_tc_ok,ite_true]
#print axioms accepted
#print axioms zero
end NFG_TryInvCuts
