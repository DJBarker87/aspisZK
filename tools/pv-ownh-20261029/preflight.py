"""Revalidate the existing RDB2D cohort read-only; prepare private task inputs."""
from pathlib import Path
import json,lzma,hashlib,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-ownh-20261029'
p=R/'evidence/pv-rdb2d-20261028/rdb2d-dependency-fingerprint.json.xz'
j=json.loads(lzma.open(p).read())
for r in j['objects']:
 b=subprocess.check_output(['git','show','HEAD:'+r['source_path']]);assert hashlib.sha256(b).hexdigest()==r['source_sha256'],r['module']
code='''from pathlib import Path
import json,hashlib
j=json.loads(DATA);D=Path('/home/dombarker/project-offloads/codex-pv-ownh-20261029');old=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
e=json.loads((old/'env-J.json').read_text());assert e==j['env'],'changed inherited env'
roots=[Path(x) for x in e['LEAN_PATH'].split(':')]
def select(m):return next(p/(m.replace('.','/')+'.olean') for p in roots if (p/(m.replace('.','/')+'.olean')).exists())
for r in j['external']:assert sha(select(r['module']))==r['expected'],r['module']
for r in j['canonical_ejr']:assert sha(select(r['module']))==r['expected'],r['module']
for r in j['objects']:
 assert sha(select(r['module']))==r['object_sha256'],r['module']
 for i in r['imports']:assert sha(select(i['module']))==i['object_sha256'],(r['module'],i['module'])
D.mkdir(exist_ok=True);(D/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True);(D/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True)
(D/'env-J.json').write_bytes((old/'env-J.json').read_bytes())
print(json.dumps(dict(ok=True,external_count=len(j['external']),project_count=len(j['objects']),canonical_ejr_count=len(j['canonical_ejr']),env_sha256=sha(D/'env-J.json'),environment='identical toolchain and LEAN_PATH prefix; private new outputs prepended by standing run2',source_object_and_all_recorded_transitive_import_hashes_checked=True)))
'''.replace('DATA',repr(json.dumps(j)))
q=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert q.returncode==0,q.stderr
out=json.loads(q.stdout);out.update(inherited_fingerprint=str(p.relative_to(R)),inherited_fingerprint_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),authority='inherited EJR resolutions and h5 tracked source hashes; h6 read-only reuse')
(E/'cohort-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
