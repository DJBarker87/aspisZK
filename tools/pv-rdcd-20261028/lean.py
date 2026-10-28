from pathlib import Path
import subprocess,json,hashlib,sys,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd-20261028';D='/home/dombarker/project-offloads/codex-pv-rdcd-20261028';H='dombarker@100.108.41.90'
n=int(sys.argv[1]);m=sys.argv[2];assert 41400<=n<=41499
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean')
if not p.exists():p=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/(m.split('/')[-1]+'.lean')
s=p.read_bytes();assert s==subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
meta=dict(attempt=n,module=m,source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(s).hexdigest(),source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),authority='own tracked h5 project dependency or new PV_RDCD module; external closure preflight 5673 objects')
# Check the ID column, not substrings inside object hashes.
code='''from pathlib import Path
import json,re
n=ID
s=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/evidence/sent.txt').read_text()
a=[l for l in s.splitlines() if len(l.split())>=3 and l.split()[2]==str(n)]
b=[str(p) for d in Path('/home/dombarker/project-offloads').glob('codex-pv-*') for p in d.glob('**/*'+str(n)+'*') if (p.is_file() or p.is_dir()) and d.name!='codex-pv-rdcd-20261028' and re.search(r'(?<![0-9a-fA-F])'+str(n)+r'(?![0-9a-fA-F])',p.name)]
print(json.dumps(dict(shared=a,private=b)))
assert not a and not b,(a,b)
'''.replace('ID',str(n))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);(E/f'{n}-id-check.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2));assert r.returncode==0,r.stderr
subprocess.run(['scp','-q',str(p),H+':'+D+'/lean-sources/'+m+'.lean'],check=True)
(E/f'{n}-source.json').write_text(json.dumps(meta,indent=2)+'\n')
c=['timeout','900','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
r=subprocess.run([sys.executable,str(R/'tools/pv-rdcd-20261028/scope.py'),'lean-'+str(n),'Lean',*c])
p=E/('lean-'+str(n))/'receipt.json'
if p.exists():j=json.loads(p.read_text());j.update(meta);p.write_text(json.dumps(j,indent=2)+'\n')
sys.exit(r.returncode)
