#!/usr/bin/env python3
"""Prepare explicit reviewed recipes; never runs a prover or changes source evidence."""
import json
from pathlib import Path
E=Path(__file__).resolve().parent
R=E.parent.parent
load=lambda p:json.loads((R/p).read_text())
recipes=[]
for pre,packet,key in [('NDD','native-front1-20261028','members'),('NDF','native-front3-20261028','functions'),('NDG','native-front4-20261028','closures')]:
 directory='evidence/'+packet+'/'
 delta=load(directory+pre+'_LEDGER_DELTA.json')
 for i,row in enumerate(delta[key]):
  admitted=row.get('status',row.get('local_status')) in ['CLOSED-local','CLOSED-CONDITIONAL']
  spec=dict(id=f'{pre}::refresh::{i:02}',packet=packet,delta=directory+pre+'_LEDGER_DELTA.json',delta_key=key,index=i,function=row['function'],admit=admitted,domain=row.get('domain','No closed native domain'),remaining=row.get('obstacle') or row.get('remaining') or 'Caller domain and physical interpretation remain OPEN.',native=[],theorems=[],rule14_dependencies=[],feature_scope='program' if pre=='NDG' else 'core-helper' if pre=='NDD' else 'library-helper')
  if admitted:
   if pre=='NDD':
    spec['native']=[{'attempt':row['kani_attempt'],'positive':True},{'attempt':row['negative_control'],'positive':False}]
    spec['theorems']=[{'name':row['lean_theorem'],'attempt':row['lean_attempt']}]
   elif pre=='NDF':
    pairs={'opening':([2],[3],'NDF_OpeningBridge.reference',9),'batch_key_at':([10,11],[12,13],'NDF_ScalarBridge.key',3),'same_batch_index':([14,15],[16,17],'NDF_ScalarBridge.same_index',3),'same_batch_leaf':([18,19,22],[20,21,23],'NDF_LeafBridge.same_leaf',4),"Prefix<'a>::record":([48],[49],'NDF_RecordBridge.reference',16),"ValidatedRecord<'a>::framed":([38],[39],'NDF_ScalarBridge.framed',3)}
    short=row['function'].split('.rs::')[1]
    pos,neg,theorem,attempt=pairs[short]
    spec['native']=[dict(attempt=f'NDF_K{n:03}',positive=p) for p,ns in [(True,pos),(False,neg)] for n in ns]
    spec['theorems']=[dict(name=theorem,attempt=f'NDF_L{attempt:03}')]
   else:
    spec['native']=[dict(attempt=a,positive=(j==0)) for j,a in enumerate(row['kani'])]
    spec['theorems']=[dict(name=row['theorem'],attempt='NDG_L003' if 'MetadataBridge' in row['theorem'] else 'NDG_L007')]
   spec['rule14_dependencies']=['Exact selected property and its scalar/fixed-array callees contain no Option<fn>, observer, function-pointer value or comparison; no mark/release-observer receipt consumed. KMX is data-pointer copying, not a function-pointer observation.']
   spec['remaining']=('Same native/cohort caller carrier and installed dictionary association remain OPEN. '+spec['remaining'])
  recipes.append(spec)
# Record NDG's remaining members as rejected enclosing closures too.
for i,name in enumerate(load('evidence/native-front4-20261028/NDG_LEDGER_DELTA.json')['open']):
 recipes.append(dict(id=f'NDG::open::{i:02}',packet='native-front4-20261028',delta='evidence/native-front4-20261028/NDG_LEDGER_DELTA.json',delta_key='open',index=i,function=name,admit=False,domain='No complete native domain',remaining='See NDG_FRONTIER_BRIDGES.md: restricted native fragments or model-only results do not establish this enclosing body.',native=[],theorems=[],rule14_dependencies=[],feature_scope='program'))
(E/'NDK_ASSOCIATIONS.json').write_text(json.dumps(recipes,indent=2)+'\n')
