#!/usr/bin/env python3
"""Build explicit review inputs from merged lane deltas; no proof execution."""
import json
from pathlib import Path
E=Path(__file__).resolve().parent
R=E.parent.parent
load=lambda p:json.loads((R/p).read_text())
base=load('evidence/native-ledger2-20261028/NDK_LEDGER.json')
names=sorted({r['function'] for r in base['rows']})
packets={'NDE':'native-front2','NDL':'native-front1b','NDN':'native-front2b','NDI':'native-front3b','NDH':'native-front5','NDM':'native-front4b'}
recipes=[]
for pre,packet in packets.items():
 directory='evidence/'+packet+'-20261028/'
 d=load(directory+pre+'_LEDGER_DELTA.json')
 key={'NDE':'rows','NDL':'members','NDN':'rows','NDI':'new_local_closures','NDH':'closures','NDM':'local_changes'}[pre]
 for i,row in enumerate(d[key]):
  name=row['function']
  if name not in names:
   # NDI spells the module/owner locally, and has an explicit concrete
   # SolanaDigest monomorph where the inventory preserves generic H.
   tail=name.split('::',1)[1]
   if pre=='NDI':
    tail=tail.replace('SemanticTranscript<SolanaDigest>','SemanticTranscript<H>').replace('ValidatedRecord::',"ValidatedRecord<'a>::")
    matches=[n for n in names if n.endswith('::'+tail) and '/'+name.split('::')[0]+'.rs::' in n]
    assert len(matches)==1,(name,matches)
    name=matches[0]
   else:raise ValueError(name)
  status=row.get('status',row.get('after'))
  admitted=status in ['CLOSED','CLOSED-local','CLOSED-CONDITIONAL']
  inherited=pre=='NDL' and str(row.get('kani_attempt','')).startswith('NDD_')
  spec=dict(id=f'NDT::local::{pre}::{i:02}',prefix=pre,packet=packet+'-20261028',delta=directory+pre+'_LEDGER_DELTA.json',delta_key=key,index=i,function=name,reported_function=row['function'],admit=admitted and not inherited,disposition='REUSE INHERITED' if inherited else 'ADMIT LOCAL CONDITIONAL' if admitted else 'REJECT STATUS PROMOTION',domain=row.get('domain','No complete native domain'),remaining=row.get('obstacle') or row.get('remaining_lean_only_obligation') or row.get('limits') or row.get('callee_domain') or 'Caller domain, same-execution carrier/dictionary, physical interpretation and source-to-ELF remain OPEN.',native=[],theorems=[],rule14_dependency_audit='Selected static/scalar/data-pointer properties only; no Option<fn>, function-pointer value/comparison or legacy observer property is consumed. Historical mark/observer quarantine remains. Arithmetic logs retain named Lean value laws.',feature_scope='program' if pre=='NDM' else 'statement-helper' if pre in ['NDE','NDN'] else 'library-helper')
  if spec['admit']:
   if pre=='NDE':
    spec['native']=[dict(attempt=f'NDE_K{row[k]:03}',positive=p) for k,p in [('positive',True),('negative',False)]]
    spec['theorems']=[x.strip() for x in row['lean'].split(';')]
   elif pre=='NDL':
    spec['native']=[dict(attempt=row[k],positive=p) for k,p in [('kani_attempt',True),('negative_control',False)]]
    spec['theorems']={'field':['NDL_FieldCompose.cohort','NDL_FieldDecode.window'],'double':['NDL_DoubleLaw.cohort','NDL_DoubleLaw.product'],'shared_two_point_guard':['NDL_GuardRawModel.cohort']}[name.split('::')[-1]]
    spec['native'] += [dict(attempt=a,positive=(a=='NDL_K003')) for a in row.get('supporting_native',[])]
   elif pre=='NDN':
    spec['native']=[dict(attempt=f'NDN_K{n:03}',positive=p) for n,p in [(1,True),(2,False),(3,True),(4,False)]]
    spec['theorems']=['NDN_PackedReference.matrix','NDN_PackedFrame.result']
   elif pre=='NDI':
    spec['feature_scope']='program' if 'SemanticTranscript' in name else 'library-helper'
    spec['native']=[dict(attempt=a,positive=j%2==0) for j,a in enumerate(row['native'])]
    spec['theorems']=[row['theorem']]
    if i==3:spec['theorems']+=['NDI_TranscriptCaller.initialized_public','NDI_BorrowBridge.initial']
    if i==4:spec['theorems']+=['NDI_BatchStep.step','NDI_BatchRun.run','NDI_BatchBridge.reference','NDI_BatchCaller.canonical','NDI_BatchControl.reached']
   elif pre=='NDH':
    spec['native']=[dict(attempt=a,positive=j==0) for j,a in enumerate(row['kani'])]
    spec['theorems']=[t for ts in row['lean'].values() for t in ts]
    if name.endswith('::cm31_mul_r'):spec['feature_scope']='core-helper'
   elif pre=='NDM':
    spec['native']=[dict(attempt=f'NDM_K{n:03}',positive=n%2==1) for n in range(39,45)]
    spec['theorems']=['NDM_ZeroCut.suffix_step','NDM_ZeroSuffix.resume_suffix','NDM_ZeroCaller.checkpoint_domain','NDG_ZeroRun.value']
  recipes.append(spec)
 # Explicit string-only OPEN members are decisions, never missing evidence.
 for i,name in enumerate(d.get('open',[])):
  recipes.append(dict(id=f'NDT::open::{pre}::{i:02}',prefix=pre,packet=packet+'-20261028',delta=directory+pre+'_LEDGER_DELTA.json',delta_key='open',index=i,function=name,reported_function=name,admit=False,disposition='REJECT STATUS PROMOTION',domain='No complete native domain',remaining='See pinned '+pre+'_FRONTIER_BRIDGES.md and handoff: native caller/carrier, complete value/Result, frame or quarantined observer obligation remains.',native=[],theorems=[],rule14_dependency_audit='',feature_scope='program'))
# Carry per-member OPEN findings from continuation matrices into explicit
# decisions; do not infer closure from a prose status label.
for pre,packet in [('NDI','native-front3b'),('NDM','native-front4b'),('NDH','native-front5')]:
 path='evidence/'+packet+'-20261028/'+pre+'_FRONTIER_BRIDGES.md'
 for line in (R/path).read_text().splitlines():
  cells=[x.strip().strip('`') for x in line.split('|')[1:-1]]
  if not cells:continue
  if pre=='NDM':
   if len(cells)!=2 or not cells[1].startswith('OPEN'):continue
   short=cells[0];matches=[n for n in names if n.startswith('programs/r1-cost-probe/src/r1_pool_adapter') and n.endswith('::'+short)]
   assert len(matches)==1,(short,matches)
   name=matches[0];reason=cells[1];domain='No complete native caller/carrier domain'
  else:
   if len(cells)<4 or cells[2]!='OPEN':continue
   name=cells[0];reason=cells[-1];domain=cells[3] if pre=='NDI' else 'No complete native domain'
  existing=next((s for s in recipes if s['prefix']==pre and s['function']==name),None)
  if existing:
   if not existing['admit']:existing['remaining']=reason;existing['matrix_evidence']=path
   continue
  assert name in names,name
  recipes.append(dict(id=f'NDT::matrix::{pre}::{len(recipes):03}',prefix=pre,packet=packet+'-20261028',delta=path,delta_key=None,index=None,function=name,reported_function=name,admit=False,disposition='REJECT STATUS PROMOTION',domain=domain,remaining=reason,native=[],theorems=[],rule14_dependency_audit='',feature_scope='program',matrix_evidence=path))
(E/'NDT_ASSOCIATIONS.json').write_text(json.dumps(recipes,indent=2)+'\n')
