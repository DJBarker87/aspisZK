from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;P=E.parent/'terminal4-20261108';start=int(sys.argv[1]);mapping={};B='/home/dombarker/project-offloads/codex-cx-terminal5-20261108'
base_sources=['NKR_seed.py','NKR_NKI_EXPORT.json','NKR_NKN_EXPORT.json','NKR_GATE_SOURCES.json','NKR_EXPECTED_IMPORTS.jsonl','NKR_AUDIT_ROOTS.json','NKR_AUDIT_MODULES.json']
def clone(old,a):
 x=json.loads((P/(old+'.json')).read_text());x=json.loads(json.dumps(x).replace('NKI','NKR').replace('codex-cx-terminal4','codex-cx-terminal5'));x.pop('deps_fingerprint',None);x.pop('source_revision',None);x.pop('source_tree_dirty',None);prev=x['attempt'];x['attempt']=a;x['command']=[t.replace(prev,a)for t in x['command']];x['env']['LEAN_PATH']=':'.join(json.loads((E/'NKR_PATH.json').read_text()));x['env']['CARGO_TARGET_DIR']=B+'/NKR_target';x['collect']=[t.replace(prev,a)for t in x.get('collect',[])];return x
for n,(mode,old,source)in enumerate([('driver','NKI_L087','NKR_Driver.lean'),('proof_driver','NKI_L088','NKR_ProofDriver.lean'),('link','NKI_L089','NKR_link.py'),('combined','NKI_L090','NKR_COMBINED_IMPORT.lean'),('fixtures','NKI_L091','NKR_batch.py'),('scan','NKI_L092','NKR_batch.py')]):
 a=f'NKR_L{start+n:03d}';x=clone(old,a);x['sources']=[source]+base_sources+(['NKR_gate_setup.py']if mode=='link'else[]);x['expected_time']='Focused first combined gate '+mode+' with unchanged hardened walker';(E/(a+'.json')).write_text(json.dumps(x));mapping[mode]=a
for n in range(28):
 a=f'NKR_L{start+6+n:03d}';x=clone('NKI_L093',a);mode='proof'+str(n);x['module']='NKR_'+mode;x['command']=['python3','NKR_batch.py',mode,a];x['sources']=['NKR_batch.py']+base_sources;x['collect_globs']=['NKR_audit/'+mode+'/*'];x['expected_time']='One disjoint complete-root raw axioms partition '+str(n)+' of28; no unchanged full replay';(E/(a+'.json')).write_text(json.dumps(x));mapping[mode]=a
(E/'NKR_GATE_ATTEMPTS.json').write_text(json.dumps(mapping,indent=1));print('34 capped first-gate scopes configured')
