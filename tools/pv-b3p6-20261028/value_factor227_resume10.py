"""D411 split at existing exact array-store stage boundaries; no limit changes."""
from pathlib import Path
import re,json,sys,hashlib
D=Path('evidence/pv-b3p6-20261028'); L=D/'lean'; O=D/'resume10'; O.mkdir(exist_ok=True)
raw=(L/'PV_B3P_P227_10.lean').read_text(); a=raw.index('def reference_terminal.add_value_lanes');b=raw.index('\n/--',a);decl=raw[a:b].strip();body=decl.split(':= do\n',1)[1];lines=body.splitlines()
keys=['q8','q23','q38','q53','q68','q83','q98','q108','q120','q132','q144','q156','q168','packed1']
starts=[0]+[next(i for i,line in enumerate(lines)if re.match(r'  let '+key+r' ←',line))for key in keys]
params='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
header='''namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result ControlFlow Error
set_option autoImplicit false
'''
opaque='aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row'
files={};records=[]
# Each suffix is the exact original tail with only live-in names renamed to state.
for i in reversed(range(1,15)):
 tail='\n'.join(lines[starts[i]:]);incoming=re.findall(r'  let (range\d*) ← Array.update','\n'.join(lines[:starts[i]]))
 incoming=incoming[-1] if incoming else 'range'
 tail=re.sub(r'\b'+incoming+r'\b','range_input',tail);tail=re.sub(r'\brange_selector\b','range_selector',tail)
 m=f'PV_B3P_ValueTail10{i:02}227';fn=f'value_source_tail10_{i:02}';nxt=f'value_source_tail10_{i+1:02}';stage=f'value_owned_stage9_{i:02}';ctx=f'value_read_context9_{i:02}'
 imports=f'import PV_B3P_ValueRead9{i:02}227\nimport PV_B3P_DigestCpsEq9227\n'+(f'import PV_B3P_ValueTail10{i+1:02}227\n'if i<14 else '')
 s=imports+header+f'\ndef {fn} {params} (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) : Result (Array aspis_core.field.QM31 24#usize) := do\n'+tail+'\n'
 s+='\nattribute [local irreducible] '+opaque+(' '+nxt if i<14 else '')+'\n'
 s+=f'\ntheorem value_source_equation10_{i:02} {params} (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) :\n    {fn} packed openings selectors range_selector range_input =\n      {stage} packed openings selectors (range_selector,range_input)'+(f' >>= (fun next => {nxt} packed openings selectors next.1 next.2)'if i<14 else '')+' := by\n'
 s+=f'  unfold {fn} {stage} {ctx}\n'
 if i<14:
  s+='  conv_rhs => simp only [bind_assoc, bind_tc_ok]\n'
  count=len(re.findall(r'^  let .+? ←','\n'.join(lines[starts[i]:starts[i+1]]),re.M))
  for j in range(count):s+='  apply bind_equal9\n'+f'  intro head_{j}\n'
  s+=f'  unfold {nxt}\n  rfl\n'
 else:s+='  rfl\n'
 s+=f'\n#print axioms value_source_equation10_{i:02}\nend PV_B3P_Binding10227\n';files[m]=s
 records.append(dict(stage=i,module=m,source_lines=[starts[i]+1,len(lines)],live_in_range=incoming,theorem=f'value_source_equation10_{i:02}'))
m='PV_B3P_ValueEntry10227';s='import PV_B3P_ValueTail1001227\nimport PV_B3P_ValueRead900227\n'+header
s+='\nattribute [local irreducible] '+opaque+' value_source_tail10_01\n'
s+=f'''\ntheorem value_source_equation10_00 {params} :
    reference_terminal.add_value_lanes packed openings selectors =
      value_owned_stage9_00 packed openings selectors >>= (fun next => value_source_tail10_01 packed openings selectors next.1 next.2) := by
  unfold reference_terminal.add_value_lanes value_owned_stage9_00 value_read_context9_00
  conv_rhs => simp only [bind_assoc, bind_tc_ok]
'''
count=len(re.findall(r'^  let .+? ←','\n'.join(lines[:starts[1]]),re.M))
for j in range(count):s+='  apply bind_equal9\n'+f'  intro head_{j}\n'
s+='  unfold value_source_tail10_01\n  rfl\n\n#print axioms value_source_equation10_00\nend PV_B3P_Binding10227\n';files[m]=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(source_sha256=hashlib.sha256(raw.encode()).hexdigest(),stage_boundaries=starts,modules=list(files),stages=records,strategy='named exact-source suffix equations; one stage per module; local irreducibility; no whole body reduction or raised limits',credit='entry factorization only; not exhaustive shipped-source structural binding')
p=O/'value-factorization.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
