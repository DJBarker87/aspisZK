from pathlib import Path
E=Path(__file__).resolve().parent
s='''import NEB_CMCalls
import NEB_QMCalls
import NEB_WideCalls
import NEB_ByRCalls
import NEB_PureFrame
set_option autoImplicit false
namespace NEB_FieldFrames
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
'''
items=[('cm_mul','(x y : NC) (hx : canonC x) (hy : canonC y)','CM31.mul x y','canonC z','cw z=mulC (cw x) (cw y)','LPi_FieldValues.cm_mul x y hx hy'),('qm_mul','(x y : NQ) (hx : canonQ x) (hy : canonQ y)','QM31.mul x y','canonQ z','qw z=mulQ (qw x) (qw y)','LPi_TowerValues.qm_mul x y hx hy'),('wide_mul','(x y : NE) (hx : canonE x) (hy : canonE y)','wide_exact.WideExact.mul x y','canonE z','ew z=mulE (ew x) (ew y)','LPi_TowerValues.wide_mul x y hx hy'),('by_r','(x : NC) (hx : canonC x)','mul_by_r x','canonC z','cw z=byR (cw x)','LPi_FieldValues.by_r x hx'),('mul_u','(x : NQ) (hx : canonQ x)','wide_exact.mul_u x','canonQ z','qw z=mulU (qw x)','LPi_TowerValues.mul_u x hx'),('cm_scale','(x : NC) (scalar : U32)','CM31.mul_m31 x scalar','canonC z','cw z=((x.a.val*scalar.val)%2147483647,(x.b.val*scalar.val)%2147483647)','LPi_MixedValues.cm_m31 x scalar'),('qm_scale','(x : NQ) (scalar : U32)','QM31.mul_m31 x scalar','canonQ z','qw z=(((x.c0.a.val*scalar.val)%2147483647,(x.c0.b.val*scalar.val)%2147483647),((x.c1.a.val*scalar.val)%2147483647,(x.c1.b.val*scalar.val)%2147483647))','LPi_MixedValues.qm_m31 x scalar'),('wide_scale','(x : NE) (scalar : U32)','wide_exact.WideExact.mul_m31 x scalar','canonE z','ew z=(NBG_FieldDischarge.scaleQ (qw x.c0) (scalar.val%2147483647),NBG_FieldDischarge.scaleQ (qw x.c1) (scalar.val%2147483647))','NBG_FieldDischarge.wide_scale x scalar'),('wide_mixed','(x : NE) (y : NQ) (hx : canonE x)','wide_exact.WideExact.mul_qm31 x y','canonE z','ew z=(mulQ (qw x.c0) (NBG_FieldDischarge.modQ (qw y)),mulQ (qw x.c1) (NBG_FieldDischarge.modQ (qw y)))','NBG_FieldDischarge.wide_qm x y hx')]
for name,args,call,canon,value,source in items:
 body='FIo_Native.aspis_core.field.'+call
 s+=f'''\n/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem {name} {{S Event : Type}} (state : S) {args} :
    ∃ z, {body}=ok z ∧ {canon} ∧
      {value} ∧
      NEB_PureFrame.run (Event:=Event) state ({body})=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := {source}
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩
'''
s+='\n'.join('#print axioms '+n for n,*_ in items)+'\nend NEB_FieldFrames\n';(E/'NEB_FieldFrames.lean').write_text(s)
