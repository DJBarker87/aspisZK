from pathlib import Path
import subprocess,hashlib,json,tarfile
B=Path(__file__).resolve().parent
R=Path('/home/dombarker/project-offloads')
inputs=R/'s4-fromfn-guard-inline-charon-v1-20261022/inputs'
pins={'aeneas':'946d65f31e14d65efdbad996d4f706a612fcc62b2a35331fa9e2d525c596e988','charon':'d8e799da5e85805ae21798bb19ed93f8a0d1a295cc3d82047c62b85d51dc92e8'}
source=B/'XRa_toolchain';source.mkdir(exist_ok=False)
for name,h in pins.items():
 p=inputs/(name+'-exact-source.tar.gz')
 assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==h
 with tarfile.open(p) as t:t.extractall(source,filter='data')
 print('ARCHIVE',name,h,p.stat().st_size,flush=True)
p=B/'XRa_aeneas.patch';assert hashlib.sha256(p.read_bytes()).hexdigest()=='5abaafc2d345511dda0eb96cd40154daff137f79dc4bcfa8247a45acea639c9c'
a=source/'aeneas'
def run(cmd,cwd):
 print('COMMAND',cmd,flush=True);return subprocess.check_output(cmd,cwd=cwd,text=True).strip()
run(['git','init','-q'],a)
run(['git','add','-f','--all'],a)
print('BASE_TREE',run(['git','write-tree'],a),flush=True)
run(['git','apply','--check','--unidiff-zero',str(p)],a)
run(['git','apply','--unidiff-zero',str(p)],a)
run(['git','add','-f','--all'],a)
tree=run(['git','write-tree'],a);print('PATCHED_TREE',tree,flush=True)
assert tree=='5a843e70672e4139232b2fdcb52a0c1fbd4b1619',tree
rows=[]
for n in ['aeneas','charon']:
 for p in sorted((source/n).rglob('*')):
  if '.git' in p.parts or not (p.is_file() or p.is_symlink()):continue
  rows.append({'path':str(p.relative_to(source)),'symlink':str(p.readlink()) if p.is_symlink() else None,'sha256':None if p.is_symlink() else hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.lstat().st_size})
(B/'XRa_recovered_sources.json').write_text(json.dumps({'patched_tree':tree,'archives':pins,'files':rows},indent=2)+'\n')
print('SOURCE_RECOVERY_PASS',len(rows),flush=True)
