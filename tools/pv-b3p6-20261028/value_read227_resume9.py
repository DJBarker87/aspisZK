"""Partition the exact emitted value body at array-store boundaries.
No field expression is changed; next stages receive the full selector/array pair.
"""
from pathlib import Path
import re,json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume9';raw=(L/'PV_B3P_P227_10.lean').read_text();a=raw.index('def reference_terminal.add_value_lanes');b=raw.index('\n\nend ',a);decl=raw[a:b].strip();body=decl.split(':= do\n',1)[1];lines=body.splitlines()
keys=['q8','q23','q38','q53','q68','q83','q98','q108','q120','q132','q144','q156','q168','packed1']
starts=[0]+[next(i for i,line in enumerate(lines)if re.match(r'  let '+key+r' ←',line))for key in keys]
assert starts==sorted(starts)
chunks=['\n'.join(lines[a:b])for a,b in zip(starts,starts[1:]+[len(lines)])];assert len(chunks)==15
header='''namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
abbrev ValueState9 := aspis_core.field.QM31 × Array aspis_core.field.QM31 33#usize
'''
params='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
readtype='({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)'
files={'PV_B3P_ValueReadTypes9227':'import PV_B3P_P227_10\nimport PV_B3P_ReadFunctions9227\n'+header+'end PV_B3P_Binding9227\n'};records=[]
header=header.replace('abbrev ValueState9 := aspis_core.field.QM31 × Array aspis_core.field.QM31 33#usize\n','')
for i,ch in enumerate(chunks):
 module=f'PV_B3P_ValueRead9{i:02}227';ctx=f'value_read_context9_{i:02}';old=f'value_owned_stage9_{i:02}';direct=f'value_direct_stage9_{i:02}';law=f'value_stage_read_binding9_{i:02}'
 if i==0:ch+='\n  Result.ok (range_selector,range)'
 elif i<14:
  # Incoming array is the first range identifier referenced, the final update binds the output.
  incoming=re.search(r'Array.update (range\d*)\b',ch)[1];out=re.findall(r'  let (range\d*) ← Array.update',ch)[-1]
  ch=re.sub(r'\b'+incoming+r'\b','state.2',ch)
  ch=re.sub(r'\brange_selector\b','state.1',ch)
  ch+='\n  Result.ok (state.1,'+out+')'
 else:
  ch=re.sub(r'\brange66\b','state.2',ch)
 ch=ch.replace('reference_terminal.read227','source_read')
 rtype='Result (Array aspis_core.field.QM31 24#usize)'if i==14 else'Result ValueState9'
 pp=params+(' (state : ValueState9)'if i else'');args='packed openings selectors'+(' state'if i else'')
 s='import PV_B3P_ValueReadTypes9227\n'+header+f'''\ndef {ctx} (source_read : {readtype}) {pp} : {rtype} := do
{ch}

def {old} {pp} : {rtype} :=
  {ctx} @reference_terminal.read227 {args}

def {direct} {pp} : {rtype} :=
  {ctx} (fun values i => Array.index_usize values i) {args}

theorem {law} {pp} :
    {old} {args} = {direct} {args} :=
  congrArg (fun (source_read : {readtype}) => {ctx} @source_read {args}) read_function_binding
#print axioms {law}
end PV_B3P_Binding9227
'''
 files[module]=s;records.append(dict(module=module,stage=i,source_lines=[starts[i]+1,(starts+[len(lines)])[i+1]],read_occurrences=ch.count('source_read'),theorem=law))
imports=''.join(f'import PV_B3P_ValueRead9{i:02}227\n'for i in range(15));s=imports+header
for kind in ['owned','direct']:
 s+=f'\ndef value_{kind}_sequence9 {params} : Result (Array aspis_core.field.QM31 24#usize) := do\n'
 for i in range(14):s+=f'  let s{i} ← value_{kind}_stage9_{i:02} packed openings selectors'+(f' s{i-1}'if i else'')+'\n'
 s+=f'  value_{kind}_stage9_14 packed openings selectors s13\n'
s+='\nattribute [local irreducible] '+' '.join(f'value_{kind}_stage9_{i:02}'for kind in ['owned','direct']for i in range(15))+'\n'
s+=f'''\ntheorem value_sequence_read_binding9 {params} :
    value_owned_sequence9 packed openings selectors = value_direct_sequence9 packed openings selectors := by
  unfold value_owned_sequence9 value_direct_sequence9
'''
for i in range(15):s+=f'  simp only [value_stage_read_binding9_{i:02}]\n'
s+='\n#print axioms value_sequence_read_binding9\nend PV_B3P_Binding9227\n';files['PV_B3P_ValueReadSequence9227']=s
s='import PV_B3P_ValueReadSequence9227\nimport PV_B3P_Ordered227\nimport PV_B3P_DigestCpsEq9227\n'+header+'open PV_B3P_Ordered227\n'
s+='\nattribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row '+ ' '.join(f'value_owned_stage9_{i:02} value_read_context9_{i:02}'for i in range(15))+'\n'
s+=f'''\ntheorem value_entry_factor9 {params} :
    reference_terminal.add_value_lanes packed openings selectors = value_owned_sequence9 packed openings selectors := by
  delta reference_terminal.add_value_lanes
  conv_rhs => unfold value_owned_sequence9
'''
for i,ch in enumerate(chunks):
 s+=f'  conv_rhs => simp only [value_owned_stage9_{i:02},value_read_context9_{i:02},bind_assoc,bind_tc_ok]\n'
 if i<14:
  count=len(re.findall(r'^  let .+? ←',ch,re.M))
  for j in range(count):s+=f'  apply bind_equal9\n  intro value_head_{i}_{j}\n'
 else:s+='  rfl\n'
s+=f'''\ntheorem add_value_read_binding9 {params} :
    reference_terminal.add_value_lanes packed openings selectors = value_direct_sequence9 packed openings selectors :=
  (value_entry_factor9 packed openings selectors).trans
    (value_sequence_read_binding9 packed openings selectors)
#print axioms value_entry_factor9
#print axioms add_value_read_binding9
end PV_B3P_Binding9227
''';files['PV_B3P_ValueReadBridge9227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
record=dict(source_module='PV_B3P_P227_10',source_sha256=hashlib.sha256(raw.encode()).hexdigest(),exact_emitted_body_partition=True,body_token_roundtrip=''.join(body.split())==''.join('\n'.join(chunks).split()),stages=records,modules=list(files),credit='read substitution only; source loop unrolling and frame binding still separate')
p=O/'value-read-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(modules=list(files),read_occurrences=sum(r['read_occurrences']for r in records))))
