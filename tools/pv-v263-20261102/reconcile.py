from pathlib import Path
import subprocess,json,hashlib,re,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-v263-20261102';plan=json.load(open(E/'build-plan.json'));records=[v for p in sorted(E.glob('modules-*.json')) for v in json.load(open(p))];accepted=[v for v in records if v['accepted']]
for v in accepted:
 p=R/plan['modules'][v['module']]['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==v['source_sha256'];assert all(not re.search(r'sorryAx|axiom.*\[(?!.*(?:propext|Classical.choice|Quot.sound))',s) for s in v['axioms'])
code='''import pathlib,json,hashlib,sys,subprocess
x=json.load(sys.stdin);p=pathlib.Path(x['workspace']);checks=[]
for v in x['records']:
 m=v['module'].replace('.','/');s=p/'sources'/(m+'.lean');o=p/'objects'/(m+'.olean');checks.append(dict(module=v['module'],source=hashlib.sha256(s.read_bytes()).hexdigest()==v['source_sha256'],object=hashlib.sha256(o.read_bytes()).hexdigest()==v['object_sha256']))
r=subprocess.run(['systemctl','--user','list-units','--plain','--no-legend','--state=running','pv66-lean-*','pv-v263-native-*'],text=True,capture_output=True);print(json.dumps(dict(checks=checks,live_scope_output=r.stdout,scope_check_exit=r.returncode)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(workspace=plan['workspace'],records=accepted)),text=True,capture_output=True,check=True);x=json.loads(r.stdout);assert all(v['source'] and v['object'] for v in x['checks']);assert x['scope_check_exit']==0 and not x['live_scope_output'];x.update(failed_sources_retained=[v['source_sha256'] for v in records if not v['accepted']],axiom_audit_kind='summary-based #print axioms, not raw walk or release audit',next_lean_id=79907,audit_ids_unused=[79997,79998,79999],next_native_id='N90122',rows_removed=[]);(E/'reconciliation.json').write_text(json.dumps(x,indent=2)+'\n');print('read-only accepted source/object and no-live-scope reconciliation PASS')
