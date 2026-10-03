#!/usr/bin/env python3
"""Strict structural checks for selected R434 helper AST nodes."""
import hashlib,json
from pathlib import Path
ROOT=Path.cwd(); OUT=ROOT/'.r21-scratch/r435-counted-fold-helper-guards/source-shape-audit'
SRC=ROOT/'.r21-scratch/r434-actual-fold-control/root-launch-a/saved-output/R434ActualFoldUbHelpers.llbc'
EXPECTED='7c03a7576da2d380749bdd48a9ded791e4563d6fb3b6834ef4d15665f479b96e'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
doc=json.loads(SRC.read_text()); tr=doc['translated']; assert sha(SRC)==EXPECTED and doc.get('has_errors') is False
defs={}
def walk(x):
 if isinstance(x,dict):
  h=x.get('HashConsedValue')
  if isinstance(h,list) and len(h)==2: defs[h[0]]=h[1]
  for v in x.values(): walk(v)
 elif isinstance(x,list):
  for v in x: walk(v)
walk(tr)
def resolve(x):
 if isinstance(x,dict):
  if set(x)=={'Deduplicated'}:
   i=x['Deduplicated']; return {'Deduplicated':i,'value':resolve(defs[i])}
  if set(x)=={'HashConsedValue'}:
   i,v=x['HashConsedValue']; return {'HashConsedValue':i,'value':resolve(v)}
  return {k:resolve(v) for k,v in x.items()}
 if isinstance(x,list): return [resolve(v) for v in x]
 return x
def stmt(fid,i): return tr['fun_decls'][fid]['body']['Structured']['body']['statements'][i]
def check(ok,msg):
 if not ok: raise AssertionError(msg)
def assignment(s):
 k=s['kind']; check(isinstance(k,dict) and 'Assign' in k,'expected Assign'); return k['Assign']
def local(dst,n): return isinstance(dst,dict) and dst.get('kind')=={'Local':n}
f114=tr['fun_decls'][114]; f115=tr['fun_decls'][115]; a114=f114['body']['Structured']['body']['statements']; a115=f115['body']['Structured']['body']['statements']
d,r=assignment(a114[5]); check(local(d,3) and r['BinaryOp'][0]=='Ge' and r['BinaryOp'][1]['Copy']['kind']=={'Local':1} and r['BinaryOp'][2]['Copy']['kind']=={'Local':2},'114 Ge shape')
d7,r7=assignment(a115[7]); d9,r9=assignment(a115[9]); d10,r10=assignment(a115[10]); d13,r13=assignment(a115[13])
check(local(d7,8) and r7['UnaryOp'][0]['Cast']['Scalar']==[{'UInt':'Usize'},{'UInt':'U64'}] and r7['UnaryOp'][1]['Copy']['kind']=={'Local':1},'115 stmt7 cast')
check(local(d9,9) and r9['UnaryOp'][0]['Cast']['Scalar']==[{'UInt':'Usize'},{'UInt':'U64'}] and r9['UnaryOp'][1]['Copy']['kind']=={'Local':2},'115 stmt9 cast')
check(local(d10,7) and r10['BinaryOp'][0]=='AddChecked' and r10['BinaryOp'][1]['Move']['kind']=={'Local':8} and r10['BinaryOp'][2]['Move']['kind']=={'Local':9},'115 stmt10 AddChecked')
proj=r13['Use'][0]['Copy']['kind']['Projection']; check(local(d13,6) and proj[1]=={'Field':[{'Tuple':2},1]} and proj[0]['kind']=={'Local':7},'115 stmt13 flag field')
sw=a115[15]['kind']['Switch']['If']; then=sw[1]['statements']; other=sw[2]['statements']
check(sw[0]['Copy']['kind']=={'Local':6} and not then,'115 stmt15 branch condition/empty branch')
check(bool(other) and other[-1]['kind']=='Return','115 other branch ends Return')
tail=a115[16:]; check(bool(tail) and tail[-1]['kind']=={'Abort':'UndefinedBehavior'},'115 later top-level tail ends Abort')
result={'source_path':str(SRC.relative_to(ROOT)),'source_sha256':sha(SRC),'functions':{
 '114':{'name':f114['item_meta']['name'],'span':f114['item_meta']['span'],'signature_resolved':resolve(f114['signature']),'opaque_in_R431':True,'comparison_stmt_index':5,'comparison_stmt':a114[5],'switch_stmt_index':6,'switch_stmt':a114[6]},
 '115':{'name':f115['item_meta']['name'],'span':f115['item_meta']['span'],'signature_resolved':resolve(f115['signature']),'opaque_in_R431':True,'stmt7_cast':a115[7],'stmt9_cast':a115[9],'stmt10_checked_add':a115[10],'stmt13_tuple_flag_read':a115[13],'stmt15_switch':a115[15],'switch_other_arm_last_kind':other[-1]['kind'],'post_switch_failure_tail':tail,'post_switch_tail_last_kind':tail[-1]['kind']}},
 'assertions_passed':['114 Ge copies local1/local2','115 casts Usize locals1/2 to U64 locals8/9','115 AddChecked moves locals8/9 into local7','115 copies tuple field1 into local6','115 Switch tests local6; first arm empty, other arm ends Return','later top-level tail remains and ends Abort UndefinedBehavior'],
 'boundary':'AST shape only; no equivalence of overflow flag or branch to a modeled rejection/panic is asserted.'}
(OUT/'source-shape-comparison.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print('source-shape assertions passed:',len(result['assertions_passed']))
