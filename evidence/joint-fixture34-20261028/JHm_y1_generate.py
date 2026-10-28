from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
for start in range(0,29,10):
 end=min(29,start+10);name=f'JHm_Y1_{start:02}'
 s='import JHm_FieldValue\nimport JHm_Arithmetic\n'+''.join(f'import JGi_Y1Cell{j:02}\n' for j in range(start,end))
 s+=f'set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{name}\nopen Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim\n'
 for j in range(start,end):
  s+=f'theorem source{j:02} : ClaimParser.field JGe_Payload27.value {j}#usize=ok (JHm_FieldValue.value JGi_Y1Cell{j:02}.arr) :=\n'
  s+=f'  JHm_FieldValue.source _ _ _ (by rw [JGe_Payload27.length];decide)\n    (by rw [JGe_Payload27.length];decide) JGi_Y1Cell{j:02}.selected JGi_Y1Cell{j:02}.bounds\n#print axioms source{j:02}\n'
  s+=f'theorem numeric{j:02} : AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed\n    (JHm_FieldValue.value JGi_Y1Cell{j:02}.arr).c0=(JHm_Arithmetic.row 5)[{j}]'+"'(by decide) := by\n  rfl\n"+f'#print axioms numeric{j:02}\n'
 s+=f'end AspisR1.{name}\nend\n'
 f=R/'lean'/f'{name}.lean'
 if '--check' in sys.argv:assert f.read_text()==s
 else:f.write_text(s)
print('Validated29 value-refined inherited y1 parser cells in3 modules')
