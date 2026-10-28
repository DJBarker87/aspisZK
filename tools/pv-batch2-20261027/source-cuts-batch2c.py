"""Exact source suffix cuts, preserving delayed pure restoration placement.
Each flat/cut equation unfolds only one fixed row before an identical suffix.
"""
from pathlib import Path
import re,sys,json,hashlib
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-batch2-20261027/batch2c')
env=(L/'PV_B2_C_ConstructorEnvironment.lean').read_text();raw=env.split('def host_weights.Weights.new',1)[1].split('  := do\n',1)[1].split('\n\n\n#print axioms host_weights.Weights.new',1)[0]
starts=[raw.index(x) for x in ['  let a2 ←','  let a18 ←','  let a34 ←','  let scp ←','  let scp1 ←']]+[len(raw)]
backs=[4,9,14,19];outs=[17,33,49,59];output={}
meta='(variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize)'
def rename(s,i):
 if i:
  s=re.sub(r'\bindex_mut_back'+str(backs[i-1])+r'\b','prevBack',s)
  s=re.sub(r'\ba'+str(outs[i-1])+r'\b','prevRow',s)
 return s
for i in reversed(range(5)):
 params=meta+(' (factors : Factors)' if i==0 else ' (prevBack : FactorRow → Factors) (prevRow : FactorRow)')
 args='variant points q q1 z '+('factors' if i==0 else 'prevBack prevRow')
 flat=rename(raw[starts[i]:],i)
 cut=flat if i==4 else rename(raw[starts[i]:starts[i+1]],i)+f'  flat{i+1} variant points q q1 z index_mut_back{backs[i]} a{outs[i]}\n'
 # Prove only the fixed prefix total, with symbolic intermediate values.
 cmds=list(re.finditer(r'^  let (.*?) (←|:=)\s*',cut,re.M));steps=[f'  unfold cut{i}'];unused=0
 for j,m in enumerate(cmds):
  name=m[1]
  if m[2]==':=':continue
  term=cut[m.end():].lstrip()
  if term.startswith('Array.index_usize'):leaf='read _ _ (by decide)'
  elif term.startswith('Array.index_mut_usize'):leaf='borrow _ _ (by decide)'
  elif term.startswith('Array.update'):leaf='write _ _ _ (by decide)'
  elif term.startswith('host_weights.double'):leaf='PV_B2_C_WeightsTotal.double _'
  elif term.startswith('aspis_core.field.QM31.mul'):leaf='⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩'
  elif term.startswith('aspis_core.field.QM31.sub'):leaf='⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩'
  else:raise Exception(term[:100])
  steps.append('  apply bind_rust _ _ ('+leaf+')')
  if name.startswith('('):steps.append('  rintro ⟨'+name[1:-1]+'⟩')
  elif name=='_':steps.append('  intro unused'+str(unused));unused+=1
  else:steps.append('  intro '+name)
 steps.append('  exact ⟨_,rfl⟩' if i==4 else f'  exact flat{i+1}_total variant points q q1 z _ _')
 imports='PV_B2_C_ConstructorRow4' if i==4 else f'PV_B2_C_ConstructorCut{i+1}'
 h=f'''import R1Z.{imports}
set_option autoImplicit false
namespace PV_B2_C_ConstructorCuts
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal
open PV_B2_C_WeightsNative PV_B2_C_ConstructorRows
'''
 if i==4:h+='abbrev FactorRow := Array (Array K 4#usize) 5#usize\n'
 rt='Result (core.result.Result host_weights.Weights verifier.Error)'
 s=h+f'def flat{i} {params} : {rt} := do\n'+flat+f'\ndef cut{i} {params} : {rt} := do\n'+cut+f'''
/-- Only one fixed-row prefix is compared; the remaining flat suffix is identical. -/
theorem flat{i}_eq_cut{i} {params} : flat{i} {args} = cut{i} {args} := by
  rfl

theorem cut{i}_total {params} : RustOk (cut{i} {args}) := by
'''+ '\n'.join(steps)+f'''

theorem flat{i}_total {params} : RustOk (flat{i} {args}) := by
  rw [flat{i}_eq_cut{i}]
  exact cut{i}_total {args}
#print axioms flat{i}_eq_cut{i}
#print axioms cut{i}_total
#print axioms flat{i}_total
end PV_B2_C_ConstructorCuts
'''
 output[L/f'PV_B2_C_ConstructorCut{i}.lean']=s
for p,s in output.items():
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
p=E/'SOURCE-CUT-PREFLIGHT.json';r=dict(scope='exact suffixes preserving delayed pure restorations; only fixed-row prefixes evaluated symbolically',outputs={str(p):hashlib.sha256(s.encode()).hexdigest() for p,s in output.items()})
if '--check' in sys.argv:assert json.loads(p.read_text())==r
else:p.write_text(json.dumps(r,indent=2)+'\n')
