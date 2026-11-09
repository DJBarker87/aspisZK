#!/usr/bin/env python3
"""P1d retry spec: copy a P1c spec unchanged (same selection, same overflow-checks-on env) except run id, host base,
PCQC_ -> PCQE_, and the Aeneas binary (patched b59d5188-extended -> rebuilt ORIGINAL 959659a6, P4c host path).
Optional 5th arg: JSON file {"start_from":[...]} to split roots (changed shape).
Usage: python3 PCQE_make_spec.py <old_spec> <old_run> <new_run> [roots_json]"""
import json,sys,re
from pathlib import Path
E=Path(__file__).resolve().parent
old,oldrun,new=sys.argv[1:4]
t=Path(old).read_text().replace(oldrun,new)
t=t.replace('/home/dombarker/project-offloads/codex-pc-prov-p1c-20261109','/home/dombarker/project-offloads/codex-pc-prov-p1d-20261109').replace('PCQC_','PCQE_')
s=json.loads(t)
OLD='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended'
NEW='/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'
assert s['aeneas_command'][0]==OLD
s['aeneas_command'][0]=NEW
s.pop('p1c',None)
s['p1d']=dict(earlier_run=oldrun,earlier_spec=old,aeneas='original b59d5188 rebuilt by P4c, sha256 959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3',
 charon='original XRa_bin/charon daad69be (driver efdbe5b8); the same Charon P1c used',
 note='same spec as the P1c run except run id, host base, PCQC_ -> PCQE_ and the Aeneas binary')
if len(sys.argv)>5 or len(sys.argv)==5:
  r=json.loads(Path(sys.argv[4]).read_text())['start_from']
  cmd=s['charon_command'];out=[];i=0
  # drop old --start-from pairs, insert new ones before --dest-file
  while i<len(cmd):
    if cmd[i]=='--start-from': i+=2;continue
    if cmd[i]=='--dest-file':
      for x in r: out+=['--start-from',x]
    out.append(cmd[i]);i+=1
  s['charon_command']=out;s['configuration']['start_from']=r
  s['p1d']['changed_shape']='roots split: '+', '.join(r)
(E/(new+'_spec.json')).write_text(json.dumps(s,indent=1)+'\n')
print(new,s['configuration']['namespace'])
