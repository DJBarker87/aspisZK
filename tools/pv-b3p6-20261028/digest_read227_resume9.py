"""Read binding via accepted shallow digest equations; never clone the terminal.
Each generated theorem invokes a named primitive or preceding stage law.
"""
from pathlib import Path
import re,sys,json,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume9';files={};rows=[]
header='''namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
open PV_B3P_Success227
set_option autoImplicit false
'''
params='''(public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
for i in range(4,24):
 imp=f'PV_B3P_DigestStage{i:02}227';raw=(L/(imp+'.lean')).read_text();decl=raw[raw.index('def digest_stage_'):raw.index('\nattribute [local irreducible]')].strip();prefix,body=decl.split(':=',1)
 assert 'reference_terminal.digest227'in body
 ctx=f'digest_read_context9_{i:02}';direct=f'digest_direct_stage9_{i:02}';law=f'digest_stage_read_binding9_{i:02}';module=f'PV_B3P_DigestRead9{i:02}227'
 readtype='Array (Array U32 8#usize) 20#usize → Usize → Result (Array U32 8#usize)'
 body=body.replace('reference_terminal.digest227','source_read')
 s=f'import {imp}\nimport PV_B3P_ReadFunctions9227\n'+header+f'''\ndef {ctx} (source_read : {readtype}) {params}
    (output : Digest8Q) : Result Digest8Q := {body}

def {direct} {params} (output : Digest8Q) : Result Digest8Q :=
  {ctx} (fun values i => Array.index_usize values i) public1 openings selectors output

theorem {law} {params} (output : Digest8Q) :
    digest_stage_{i:02} public1 openings selectors output =
      {direct} public1 openings selectors output :=
  congrArg (fun source_read => {ctx} source_read public1 openings selectors output) digest_function_binding
#print axioms {law}
end PV_B3P_Binding9227
'''
 files[module]=s;rows.append(dict(module=module,stage=i,source=imp,source_sha256=hashlib.sha256(raw.encode()).hexdigest(),read_occurrences=body.count('source_read'),theorem=law))
# Work backwards through the accepted suffix equations, keeping the next suffix opaque.
for i in reversed(range(25)):
 module=f'PV_B3P_DigestReadSuffix9{i:02}227';args='public1 openings selectors'+(' output'if i else '')
 oldstage=f'digest_stage_{i:02}';stage=f'digest_direct_stage9_{i:02}'if 4<=i<24 else oldstage
 imports=f'import PV_B3P_DigestSuffix{i:02}227\n'+(f'import PV_B3P_DigestRead9{i:02}227\n'if 4<=i<24 else '')+(f'import PV_B3P_DigestReadSuffix9{i+1:02}227\n'if i<24 else '')
 suffix=f'digest_direct_suffix9_{i:02}';nxt=f'digest_direct_suffix9_{i+1:02}';law=f'digest_suffix_read_binding9_{i:02}'
 s=imports+header+f'''\ndef {suffix} {params}'''+(' (output : Digest8Q)'if i else '')+f''' : Result Digest8Q :=
  {stage} {args}'''+(f' >>= {nxt} public1 openings selectors'if i<24 else '')+'\n'
 s+='\nattribute [local irreducible] '+stage+(' '+nxt if i<24 else '')+'\n'
 s+=f'\ntheorem {law} {params}'+(' (output : Digest8Q)'if i else '')+f''' :
    digest_suffix_{i:02} {args} = {suffix} {args} := by
  rw [digest_suffix_{i:02}_equation]
'''
 if i<24:
  if 4<=i<24:s+=f'  rw [digest_stage_read_binding9_{i:02}]\n'
  s+=f'  change ({stage} {args} >>= digest_suffix_{i+1:02} public1 openings selectors) = _\n'
  s+=f'  apply congrArg (fun next => {stage} {args} >>= next)\n  funext next\n  exact digest_suffix_read_binding9_{i+1:02} public1 openings selectors next\n'
 else:s+='  rfl\n'
 s+=f'\n#print axioms {law}\nend PV_B3P_Binding9227\n';files[module]=s
s='import PV_B3P_DigestReadSuffix900227\nimport PV_B3P_DigestBridge8227\n'+header+f'''\ntheorem public_digest_read_binding9 {params} :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_direct_suffix9_00 public1 openings selectors :=
  (digest_factor8 public1 openings selectors).trans
    (digest_suffix_read_binding9_00 public1 openings selectors)
#print axioms public_digest_read_binding9
end PV_B3P_Binding9227
''';files['PV_B3P_DigestReadBridge9227']=s
files.pop('PV_B3P_DigestReadBridge9227')  # Actual root uses separate CPS head-join generator.
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
p=O/'digest-read-bindings.json';record=dict(stages=rows,modules=list(files),strategy='accepted head equations, named primitive read equality, per-stage congruence; no whole-terminal elaboration',credit='complete read binding; other source transformations still pending')
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(modules=list(files),read_occurrences=sum(r['read_occurrences']for r in rows))))
