"""Shallow CPS head laws: leave the entire remaining continuation as a parameter.
Replaces rejected raw-tail comparisons; no large-tail equality is reduced.
"""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume10';x=json.loads((O/'value-factorization.json').read_text());raw=(L/'PV_B3P_P227_10.lean').read_text();a=raw.index('def reference_terminal.add_value_lanes');b=raw.index('\n/--',a);lines=raw[a:b].split(':= do\n',1)[1].strip('\n').splitlines();starts=x['stage_boundaries'];chunks=['\n'.join(lines[a:b])for a,b in zip(starts,starts[1:]+[len(lines)])]
params='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
header='''namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
'''
opaque='aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row'
files={}
for i in range(14):
 stage=f'value_owned_stage9_{i:02}';ctx=f'value_read_context9_{i:02}';ch=chunks[i]
 if i==0:
  ch=ch[:ch.index('  let range :=')];ret='range_selector';pp=params;fxtype='aspis_core.field.QM31';rhs='value_selector10 packed openings selectors >>= f'
  s='import PV_B3P_ValueRead900227\nimport PV_B3P_Ordered227\nimport PV_B3P_DigestCpsEq9227\n'+header+f'\ndef value_selector10 {pp} : Result aspis_core.field.QM31 := do\n'+ch+'\n  .ok range_selector\n'
 else:
  incoming=re.search(r'Array.update (range\d*)\b',ch)[1];out=re.findall(r'  let (range\d*) ← Array.update',ch)[-1];ch=re.sub(r'\b'+incoming+r'\b','range_input',ch);ret=out;pp=params+' (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize)';fxtype='Array aspis_core.field.QM31 33#usize';rhs=f'{stage} packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)'
  s=f'import PV_B3P_ValueRead9{i:02}227\nimport PV_B3P_Ordered227\nimport PV_B3P_DigestCpsEq9227\n'+header
 s+='\nattribute [local irreducible] '+opaque+'\n'
 s+=f'\ntheorem value_head_cps10_{i:02} {{β : Type}} {pp} (f : {fxtype} → Result β) :\n    (do\n'+ch+f'\n  f {ret}) = ({rhs}) := by\n'
 if i==0:s+='  unfold value_selector10\n'
 else:s+=f'  unfold {stage} {ctx}\n'
 s+='  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]\n'
 if i==0:
  s+=f'''\ntheorem value_selector_pair10 {params} :
    value_owned_stage9_00 packed openings selectors = (do
      let selector ← value_selector10 packed openings selectors
      .ok (selector,Array.repeat 33#usize aspis_core.field.QM31.ZERO)) := by
  unfold value_owned_stage9_00 value_read_context9_00 value_selector10
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
#print axioms value_selector_pair10
'''
 s+=f'\n#print axioms value_head_cps10_{i:02}\nend PV_B3P_Binding10227\n';files[f'PV_B3P_ValueCps10{i:02}227']=s
imports=''.join(f'import PV_B3P_ValueCps10{i:02}227\n'for i in range(14))+'import PV_B3P_ValueReadSequence9227\n';s=imports+header+'\nattribute [local irreducible] '+opaque+'\n'
for i in reversed(range(1,15)):
 for kind in ['owned','direct']:
  s+=f'\ndef value_{kind}_cont10_{i:02} {params} (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) : Result (Array aspis_core.field.QM31 24#usize) :=\n  value_{kind}_stage9_{i:02} packed openings selectors (selector,range_input)'
  if i<14:s+=f' >>= (fun next => value_{kind}_cont10_{i+1:02} packed openings selectors selector next.2)'
  s+='\n'
for kind in ['owned','direct']:
 s+=f'\ndef value_{kind}_cps10 {params} : Result (Array aspis_core.field.QM31 24#usize) := do\n  let selector ← value_selector10 packed openings selectors\n  value_{kind}_cont10_01 packed openings selectors selector (Array.repeat 33#usize aspis_core.field.QM31.ZERO)\n'
s+='\nattribute [local irreducible] '+' '.join(f'value_{kind}_cont10_{i:02}'for kind in ['owned','direct']for i in range(1,15))+'\n'
s+=f'''\ntheorem value_entry_cps10 {params} :
    reference_terminal.add_value_lanes packed openings selectors = value_owned_cps10 packed openings selectors := by
  unfold value_owned_cps10
  conv_rhs => rw [←value_head_cps10_00 packed openings selectors]
'''
prev='(Array.repeat 33#usize aspis_core.field.QM31.ZERO)'
for i in range(14):
 if i:
  s+=f'  conv_rhs => unfold value_owned_cont10_{i:02}; rw [←value_head_cps10_{i:02} packed openings selectors head_0_13 {prev} (fun range => value_owned_cont10_{i+1:02} packed openings selectors head_0_13 range)]\n'
 ch=chunks[i]
 if i==0:ch=ch[:ch.index('  let range :=')]
 count=len(re.findall(r'^  let .+? ←',ch,re.M))
 for j in range(count):s+='  apply bind_equal9\n'+f'  intro head_{i}_{j}\n'
 if i:prev=f'head_{i}_{count-1}'
s+='  conv_rhs => unfold value_owned_cont10_14 value_owned_stage9_14 value_read_context9_14\n'
s+='\nattribute [local irreducible] '+' '.join(f'value_{kind}_stage9_{i:02}'for kind in ['owned','direct']for i in range(15))+' value_selector10\n'
for i in reversed(range(1,15)):
 s+=f'''\ntheorem value_cont_read10_{i:02} {params} (selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) :
    value_owned_cont10_{i:02} packed openings selectors selector range_input = value_direct_cont10_{i:02} packed openings selectors selector range_input := by
  unfold value_owned_cont10_{i:02} value_direct_cont10_{i:02}
  rw [value_stage_read_binding9_{i:02}]
'''
 if i<14:
  s+=f'  apply congrArg (fun next => value_direct_stage9_{i:02} packed openings selectors (selector,range_input) >>= next)\n  funext next\n  exact value_cont_read10_{i+1:02} packed openings selectors selector next.2\n'
 s+=f'#print axioms value_cont_read10_{i:02}\n'
s+=f'''\ntheorem value_cps_read10 {params} :
    value_owned_cps10 packed openings selectors = value_direct_cps10 packed openings selectors := by
  unfold value_owned_cps10 value_direct_cps10
  apply bind_equal9
  intro selector
  exact value_cont_read10_01 packed openings selectors selector _

theorem add_value_cps_read_binding10 {params} :
    reference_terminal.add_value_lanes packed openings selectors = value_direct_cps10 packed openings selectors :=
  (value_entry_cps10 packed openings selectors).trans (value_cps_read10 packed openings selectors)
#print axioms value_entry_cps10
#print axioms value_cps_read10
#print axioms add_value_cps_read_binding10
end PV_B3P_Binding10227
''';files['PV_B3P_ValueCpsBridge10227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(modules=list(files),shape='CPS law exposes only one small head, arbitrary tail parameter; root rewrites named heads and preserves selected scalar explicitly',replaces='raw-suffix rfl comparisons rejected64017/64026; no retries of rejected shape or limit changes',credit='actual emitted value entry to CPS sequence plus immutable-read binding; exhaustive shipped-source transformations separate')
p=O/'value-cps-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
