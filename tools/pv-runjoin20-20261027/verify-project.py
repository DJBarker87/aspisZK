from pathlib import Path
import json,subprocess,shlex
E=Path(__file__).resolve().parents[2]/'evidence/pv-runjoin20-20261027'
res=json.loads((E/'endpoint-resolution.json').read_text());assert not res['unpinned']
integrity=json.loads(subprocess.check_output(['git','show',res['research_revision']+':evidence/pv-replay-20261027/receipts/final-integrity.json']))
rows=[]
for r in integrity['project_results']:
 m=r['module'].replace('/','.');src=res['resolved'].get(m)
 if src is None:continue # second replay root (V2) is not imported by this audit
 if src['sha256']!=r['source_sha256']: print('AUTHORITY MISMATCH',m,src['sha256'],r['source_sha256'])
 rows.append(dict(module=r['module'],source_expected_sha256=src['sha256'],object_expected_sha256=r['object_sha256'],authority=src['authority']))
code="""import json,sys,pathlib,hashlib
root=pathlib.Path('/home/dombarker/project-offloads/codex-pv-replay-20261027');out=[]
for r in json.load(sys.stdin):
 s=root/'sources'/(r['module']+'.lean');o=root/'objects'/(r['module']+'.olean')
 sh=hashlib.sha256(s.read_bytes()).hexdigest() if s.is_file() else None
 oh=hashlib.sha256(o.read_bytes()).hexdigest() if o.is_file() else None
 out.append(dict(**r,source_path=str(s),object_path=str(o),source_sha256=sh,object_sha256=oh,match=sh==r['source_expected_sha256'] and oh==r['object_expected_sha256']))
print(json.dumps(out))
"""
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(rows),text=True,capture_output=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'project-hash-check.json').write_text(json.dumps(out,indent=2)+'\n');print('project objects',len(out),'mismatches',[(r['module'],r['source_sha256'],r['object_sha256']) for r in out if not r['match']]);assert all(r['match'] for r in out)
