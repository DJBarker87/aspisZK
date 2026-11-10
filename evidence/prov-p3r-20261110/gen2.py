import re
src=open('PCVS_E001_emitted/raw/PCVS_wide_mul/Funs.lean').read()
body=src[src.index('namespace PCVS_wide_mul'):]
body=body.replace('namespace PCVS_wide_mul','namespace PCVS_Fresh',1).replace('end PCVS_wide_mul','end PCVS_Fresh')
head='''-- PCVS_ item (3): the frozen 4bb3b3f aspis-core WideExact mul / ZERO / ONE emission (PCVS_E001, overflow ON, features r0)
-- against the gate declarations, and the three op17 bindings stated by PRVEq_Op17_p2.
import Aeneas
import PRVEq_Op17_p2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option autoImplicit false
noncomputable section
namespace PCVS_Fresh
abbrev field.M31 := AspisR1Qm31ArithmeticProbe.field.M31
abbrev field.CM31 := AspisR1Qm31ArithmeticProbe.field.CM31
abbrev field.QM31 := AspisR1Qm31ArithmeticProbe.field.QM31
abbrev field.wide_exact.WideExact := AspisR1CurrentWideMul.field.wide_exact.WideExact
end PCVS_Fresh

'''
# strip the fresh file's own header (everything before the first namespace) already done
pairs=[('field.P','AspisR1Qm31ArithmeticProbe.field.P'),
('field.reduce_u64','AspisR1Qm31ArithmeticProbe.field.reduce_u64'),
('field.M31.add','AspisR1Qm31ArithmeticProbe.field.M31.add'),
('field.M31.double','AspisR1Qm31ArithmeticProbe.field.M31.double'),
('field.M31.sub','AspisR1Qm31ArithmeticProbe.field.M31.sub'),
('field.M31.reduce_u64','AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64'),
('field.M31.mul','AspisR1Qm31ArithmeticProbe.field.M31.mul'),
('field.mul_by_r','AspisR1Qm31ArithmeticProbe.field.mul_by_r'),
('field.CM31.add','AspisR1Qm31ArithmeticProbe.field.CM31.add'),
('field.CM31.sub','AspisR1Qm31ArithmeticProbe.field.CM31.sub'),
('field.CM31.mul','AspisR1Qm31ArithmeticProbe.field.CM31.mul'),
('field.QM31.add','AspisR1Qm31ArithmeticProbe.field.QM31.add'),
('field.QM31.mul','AspisR1Qm31ArithmeticProbe.field.QM31.mul'),
('field.QM31.sub','AspisR1CurrentWideMul.field.QM31.sub'),
('field.wide_exact.mul_u','AspisR1CurrentWideMul.field.wide_exact.mul_u'),
('field.wide_exact.WideExact.mul','AspisR1CurrentWideMul.field.wide_exact.WideExact.mul')]
tail='\nnamespace PCVS_Eq\n'
for i,(f,g) in enumerate(pairs):
    tail+=f'''theorem eq_{i} : @PCVS_Fresh.{f} = @{g} := by
  first | (trace "S1"; rfl) | (trace "S2"; with_unfolding_all rfl)
'''
tail+='''
open AspisR1PowersConcreteMul in
def toF (x : AspisR1LoopPowers.field.WideExact) : AspisR1CurrentWideMul.field.wide_exact.WideExact := toWide (AspisR1LoopPowers.toOld x)
open AspisR1PowersConcreteMul in
def fromF (x : AspisR1CurrentWideMul.field.wide_exact.WideExact) : AspisR1LoopPowers.field.WideExact := AspisR1LoopPowers.fromOld (fromWide x)

/-- binding 1: the frozen WideExact::mul (fresh emission), transported by the nominal port, is the gate field.WideExact.mul used by op17. -/
theorem bind_mul (x y : AspisR1LoopPowers.field.WideExact) :
    (do let z ← PCVS_Fresh.field.wide_exact.WideExact.mul (toF x) (toF y); ok (fromF z)) = AspisR1LoopPowers.field.WideExact.mul x y := by
  rw [eq_15]
  unfold AspisR1LoopPowers.field.WideExact.mul AspisR1PowersConcreteMul.sourceMul fromF toF
  simp only [bind_assoc, bind_tc_ok]

/-- binding 2: frozen WideExact::ZERO. -/
theorem bind_zero : fromF PCVS_Fresh.field.wide_exact.WideExact.ZERO = AspisR1LoopPowers.field.WideExact.ZERO := by
  with_unfolding_all rfl

/-- binding 3: frozen WideExact::ONE. -/
theorem bind_one : fromF PCVS_Fresh.field.wide_exact.WideExact.ONE = AspisR1LoopPowers.field.WideExact.ONE := by
  with_unfolding_all rfl

end PCVS_Eq
'''
for i in range(len(pairs)): tail+=f'#print axioms PCVS_Eq.eq_{i}\n'
tail+='#print axioms PCVS_Eq.bind_mul\n#print axioms PCVS_Eq.bind_zero\n#print axioms PCVS_Eq.bind_one\n'
open('PRVEq_WideBind_s2.lean','w').write(head+body+tail)
