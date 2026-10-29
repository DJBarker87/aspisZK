from pathlib import Path
import subprocess,json,hashlib,sys,re,base64
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rows10b-20261029';D='/home/dombarker/project-offloads/codex-pv-rows10b-20261029';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);m=sys.argv[2];assert 68600<=n<=68699 and m.startswith('R1Z/PV_ROWS10B_')
assert n<68697 or any(x in m for x in ['Audit','Combined','Replay'])
assert json.loads((E/'cohort-verification.json').read_text())['ok']
scan=subprocess.run(['ssh',H,'python3','-',subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()],input=(R/'tools/pv-rows10b-20261029/id-scan.py').read_text(),text=True,capture_output=True)
assert scan.returncode==0,scan.stdout+scan.stderr
(E/f'{n}-id-scan.json').write_text(scan.stdout)
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');rel=str(p.relative_to(R));b=subprocess.check_output(['git','show','HEAD:'+rel]);assert p.read_bytes()==b
sha=hashlib.sha256(b).hexdigest()
# Ruling (u): refuse the same source bytes after ANY failure in this line.
for f in E.glob('lean-*/receipt.json'):
 j=json.loads(f.read_text())
 assert not(j['exit']!=0 and j.get('source_sha256')==sha),'unchanged failed source '+str(f)
meta=dict(attempt=n,module=m,source_path=rel,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip(),source_sha256=sha,imports=re.findall(r'^import (\S+)',b.decode(),re.M))
code='from pathlib import Path\nimport base64\np=Path('+repr(D+'/lean-sources/'+m+'.lean')+');p.parent.mkdir(parents=True,exist_ok=True);Path('+repr(D+'/lean-objects/'+m+'.olean')+').parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode('+repr(base64.b64encode(b).decode())+'))\n'
subprocess.run(['ssh',H,'python3','-'],input=code,text=True,check=True)
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n')
cmd=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-rows10b-20261029/scope.py'),f'lean-{n}','focused Lean compilation',*cmd]);f=E/f'lean-{n}/receipt.json'
if f.exists():
 j=json.loads(f.read_text());j.update(meta);j['print_axioms']=(f.parent/'output.log').read_text();f.write_text(json.dumps(j,indent=2)+'\n')
sys.exit(r.returncode)
