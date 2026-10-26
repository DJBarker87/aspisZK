"""Collect already checked row selections without resetting another selected field.
Generated modules remain PREPARED until separately compiled and audited.
"""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2]
lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows=[r for r in json.loads((root/'evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.json').read_text()) if r['status']=='ROW-DISCHARGED(candidate)']
items=[]
for row in rows:
 n=row['op'];module=row['theorem'].split('.')[-2]
 s=(lean/(module+'.lean')).read_text()
 stmt=s.split(f'theorem op{n}_source',1)[1].split(' :=',1)[0]
 selector=re.search(r'\(([^()]*)\)\.op'+str(n)+r'\b',stmt)[1]
 if selector.startswith('selected '):selector=module+'.'+selector
 items.append((n,module,stmt,selector,row['theorem']))
imports='\n'.join('import R1Z.'+m for _,m,_,_,_ in items)
header='''set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CandidateDictionary
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PV_CB_Op229Transport.native
abbrev Late := PV_CB_Op229Transport.Late
'''
source=imports+'\n'+header+'''/-- Prepared joint value/source selection. Open callbacks remain supplied by ops.
    This is not a RunJoin or a privacy endpoint theorem. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  {ops with
'''
source+='\n'.join(f'    op{n} := @ExternalFuns.op{n} _ ({selector})'+(',' if i<len(items)-1 else '') for i,(n,_,_,selector,_) in enumerate(items))+'}\n'
source+='end R1Z.PV_CB_CandidateDictionary\n'
(lean/'PV_CB_CandidateDictionary.lean').write_text(source)
# Families provide useful focused checks before the final combined audit.
groups=[('Core',[3,77,82,83,86]),('Codecs',[71,72,80]),('Field',[100,101,110,111,114]),('Zeroizing',[127,128,130,131]),('Public',[229])]
for label,ids in groups:
 text='import R1Z.PV_CB_CandidateDictionary\n'+header.split('abbrev native',1)[0]
 for n,module,stmt,selector,theorem in items:
  if n not in ids:continue
  old=stmt
  args=stmt.split(' :\n',1)[0]
  explicit=[]
  for binder in re.findall(r'\(([^()]*)\)',args):
   if ' : ' in binder:explicit.extend(binder.split(' : ',1)[0].split())
  if n==229:explicit=['base','ops','a','b']
  if n!=229:stmt=stmt.replace('(ops : ExternalFuns)','(base : ExternalTypes) (ops : @ExternalFuns (native base))',1)
  # All exact carriers/functions are qualified, including the LatePublic transport.
  for name in ['encodeW','decodeW','encode','decode']:
   stmt=re.sub(r'(?<![\w.])'+name+r'\b',f'PV_CB_Op{n}Transport.'+name,stmt)
  if n==229:stmt=re.sub(r'(?<![\w.])source\b','PV_CB_Op229Source.source',stmt)
  stmt=re.sub(r'\([^()]*\)\.op'+str(n)+r'\b',f'(selected base ops).op{n}',stmt,count=1)
  rest=old.split(f').op{n}',1)[1].split(' =',1)[0]
  text+=f'theorem op{n}'+stmt+' := by\n'
  text+=f'  change ({selector}).op{n}'+rest+' = _\n'
  text+='  exact '+theorem+' '+' '.join(explicit)+'\n'
  text+=f'#print axioms op{n}\n'
 text+='end R1Z.PV_CB_CandidateDictionary\n'
 (lean/f'PV_CB_Candidate{label}.lean').write_text(text)
report=dict(status='PREPARED, not compiled; no extra row discharge',selected_ops=[r['op'] for r in rows],modules=['PV_CB_CandidateDictionary']+['PV_CB_Candidate'+g[0] for g in groups],purpose='Check that all independently discharged source/value selections coexist in one ExternalFuns record, preserving the common native carrier and all remaining callbacks.')
(root/'evidence/pv-cb-20261026/candidate-dictionary-prepared.json').write_text(json.dumps(report,indent=2)+'\n')
