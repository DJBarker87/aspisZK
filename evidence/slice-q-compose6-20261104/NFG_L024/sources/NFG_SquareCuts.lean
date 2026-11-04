import NFG_InverseRef.Funs
import NFG_ResultCongr
set_option autoImplicit false
namespace NFG_SquareCuts
open Aeneas Aeneas.Std Result NFG_InverseRef
/-- Both outside-Q squares and the cross product use the identical root operands. -/
theorem accepted (x out : field.QM31) (run : field.QM31.square x=ok out) :
 ∃ aa bb rotated real cross imag : field.CM31,
 field.CM31.square x.c0=ok aa ∧ field.CM31.square x.c1=ok bb ∧
 field.mul_by_r bb=ok rotated ∧ field.CM31.add aa rotated=ok real ∧
 field.CM31.mul x.c0 x.c1=ok cross ∧ field.CM31.double cross=ok imag ∧
 out=⟨real,imag⟩ := by
 unfold field.QM31.square at run
 obtain ⟨aa,ha,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨bb,hb,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨rotated,hr,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨real,hv,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨cross,hc,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨imag,hi,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 exact ⟨aa,bb,rotated,real,cross,imag,ha,hb,hr,hv,hc,hi,(Result.ok.inj run).symm⟩
#print axioms accepted
end NFG_SquareCuts
