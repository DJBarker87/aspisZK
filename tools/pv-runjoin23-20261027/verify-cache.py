"""Read-only source and object inventory for the inherited private cache."""
from pathlib import Path
import json,subprocess,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin23-20261027'
r=json.loads((E/'focused-resolution.json').read_text());mods={m:v for m,v in r['resolved'].items() if 'imports' in v}
code='''import pathlib,json,sys,hashlib
H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026');e=json.load(open(H/'runjoin23-lean/J.json'));roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];out=[]
for m,v in json.load(sys.stdin).items():
 rel=m.replace('.','/');o=next((root/(rel+'.olean') for root in roots if (root/(rel+'.olean')).is_file()),None)
 if o is None:
  out.append(dict(module=m,missing=True));continue
 real=o.resolve();s=pathlib.Path(str(real).replace('/objects/','/sources/').replace('/lean-objects/','/sources/')).with_suffix('.lean')
 sh=hashlib.sha256(s.read_bytes()).hexdigest() if s.is_file() else None
 out.append(dict(module=m,object_path=str(o),object_realpath=str(real),object_sha256=hashlib.sha256(o.read_bytes()).hexdigest(),source_path=str(s),source_sha256=sh,expected_sha256=v['sha256'],source_match=sh==v['sha256'],authority=v['authority']))
print(json.dumps(out))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(mods),text=True,capture_output=True);assert p.returncode==0,p.stderr
out=json.loads(p.stdout);(E/'focused-project-cache-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('project source checks',len(out),'unmatched',[(x['module'],x.get('source_sha256'),x.get('expected_sha256')) for x in out if not x.get('source_match')])
