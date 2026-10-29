from pathlib import Path
import importlib.util
T=Path(__file__).parent;R=T.resolve().parents[1];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
sp=importlib.util.spec_from_file_location('w',T/'write-module.py');w=importlib.util.module_from_spec(sp);sp.loader.exec_module(w)
s=(L/'PV_RunJoin_CircleR72Raw52.lean').read_text();a=s.index('def field.r24_canonical_mul\n');b=s.index('def field.QM31.mul',a);s=s[a:b];prefix=s[s.index('  let a :='):s.index('  if a >=')];body=s[s.index('                  let a1 ←'):];body='\n'.join(line[16:] if line.startswith('                ') else line for line in body.splitlines())
body=body.replace('field.','PV_RunJoin_CircleR72Raw52.field.')
text='''open PV_RunJoin_CircleNeutralShape53
abbrev Q := (U32 × U32) × (U32 × U32)
/-- Guard-free body reification of the selected neutral R72 computation. -/
def body (left right : Q) : Result (Option Q) := do
'''+prefix+body+'\n\n'
text+='''theorem canonical (left right : Q) (hl : QC left) (hr : QC right) :
    PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul left right = body left right := by
'''
for side,hyp in [('left','hl'),('right','hr')]:
 for i,(field,hfield) in enumerate([('1.1','1.1'),('1.2','1.2'),('2.1','2.1'),('2.2','2.2')]):
  text+=f'  have h{side}{i} : ¬ {side}.{field} ≥ PV_RunJoin_CircleR72Raw52.field.P := Nat.not_le.mpr {hyp}.{hfield}\n'
text+='  unfold PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul\n  simp only ['+','.join('if_neg h'+side+str(i) for side in ['left','right'] for i in range(4))+']\n  rfl\n'
w.write('PV_RunJoin_CircleNeutralR24Body53',['R1Z.PV_RunJoin_CircleNeutralShape53'],text,['body','canonical'])
