"""Collect already checked row selections without resetting another selected field.
Generated modules remain PREPARED until separately compiled and audited.
"""
from pathlib import Path
import json,re,sys
root=Path(__file__).resolve().parents[2]
lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows=[r for r in json.loads((root/'evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.json').read_text()) if r['status']=='ROW-DISCHARGED(candidate)']
items=[]
outputs={}
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
outputs[lean/'PV_CB_CandidateDictionary.lean']=source
# Families provide useful focused checks before the final combined audit.
groups=[('Core',[3,77,82,83,84,86]),('Codecs',[71,72,80]),('Field',[100,101,105,107,109,110,111,114]),('Zeroizing',[127,128,130,131]),('Public',[118,229,259])]
assert {n for n,_,_,_,_ in items}<={n for _,ids in groups for n in ids}, 'Assign each accepted row to a projection group'
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
  for name in ['encodeW','decodeW','encodeArray','decodePoints','encodeRow','decodePoint','encode','decode']:
   stmt=re.sub(r'(?<![\w.])'+name+r'\b',f'PV_CB_Op{n}Transport.'+name,stmt)
  if n==229:stmt=re.sub(r'(?<![\w.])source\b','PV_CB_Op229Source.source',stmt)
  stmt=re.sub(r'\([^()]*\)\.op'+str(n)+r'\b',f'(selected base ops).op{n}',stmt,count=1)
  rest=old.split(f').op{n}',1)[1].split(' =',1)[0]
  text+=f'theorem op{n}'+stmt+' := by\n'
  text+='  letI : ExternalTypes := native base\n'
  text+=f'  change ({selector}).op{n}'+rest+' = _\n'
  text+='  exact '+theorem+' '+' '.join(explicit)+'\n'
  text+=f'#print axioms op{n}\n'
 text+='end R1Z.PV_CB_CandidateDictionary\n'
 outputs[lean/f'PV_CB_Candidate{label}.lean']=text
audit=''.join(f'import R1Z.PV_CB_Candidate{label}\n' for label,_ in groups)
audit+='\n-- Audit both the published row laws and their joint projections.\n'
audit+=''.join(f'#print axioms {theorem}\n' for _,_,_,_,theorem in items)
audit+=''.join(f'#print axioms R1Z.PV_CB_CandidateDictionary.op{n}\n' for n,_,_,_,_ in items)
helper_plan=root/'evidence/pv-cb-20261026/RESUME3-FOCUSED-AUDIT-PLAN.json'
if helper_plan.exists():
 source_names={theorem for _,_,_,_,theorem in items}
 audit+='\n-- Generic/carrier/P6 helper audit for the newly discharged rows.\n'
 audit+=''.join(f'#print axioms {name}\n' for name in json.loads(helper_plan.read_text())['covered_declarations'] if name not in source_names)
outputs[lean/'PV_CB_CandidateAudit.lean']=audit
report=dict(status='PREPARED, not compiled; no extra row discharge',selected_ops=[r['op'] for r in rows],modules=['PV_CB_CandidateDictionary']+['PV_CB_Candidate'+g[0] for g in groups]+['PV_CB_CandidateAudit'],purpose='Check that all independently discharged source/value selections coexist in one ExternalFuns record, preserving the common native carrier and all remaining callbacks.')
outputs[root/'evidence/pv-cb-20261026/candidate-dictionary-prepared.json']=json.dumps(report,indent=2)+'\n'
if sys.argv[1:]==['--check']:
 mismatches=[str(p.relative_to(root)) for p,s in outputs.items() if not p.exists() or p.read_text()!=s]
 if mismatches:raise SystemExit('Stale generated files: '+', '.join(mismatches))
 print(f'PASS: {len(rows)} row selections, five projection groups, published-source and projection axioms audit; no Lean invocation')
elif not sys.argv[1:]:
 for p,s in outputs.items():p.write_text(s)
else:raise SystemExit('usage: candidate_dictionary.py [--check]')
