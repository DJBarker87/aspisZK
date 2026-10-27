from pathlib import Path
import subprocess,hashlib,json
B=Path(__file__).resolve().parent
S=B/'XRa_toolchain';a=S/'aeneas';tree='5a843e70672e4139232b2fdcb52a0c1fbd4b1619'
subprocess.run(['git','restore','--source='+tree,'--staged','--worktree','.'],cwd=a,check=True)
actual=subprocess.check_output(['git','write-tree'],cwd=a,text=True).strip();assert actual==tree
assert not subprocess.check_output(['git','diff','--name-only'],cwd=a,text=True).strip()
rows=[]
for n in ['aeneas','charon']:
 for p in sorted((S/n).rglob('*')):
  if '.git' in p.parts or not (p.is_file() or p.is_symlink()):continue
  rows.append({'path':str(p.relative_to(S)),'symlink':str(p.readlink()) if p.is_symlink() else None,'sha256':None if p.is_symlink() else hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.lstat().st_size})
(B/'XRa_recovered_sources.json').write_text(json.dumps({'patched_tree':tree,'files':rows},indent=2)+'\n')
print('EXACT_PATCHED_TREE',tree,'files',len(rows),flush=True)
# An image is created but never started: copy the pinned compiler dependency
# switch for native compilation under the single systemd scope, then remove
# only this stopped temporary container. No Docker build scope is launched.
image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
cid=subprocess.check_output(['docker','create',image],text=True).strip()
try:
 subprocess.run(['docker','cp',cid+':/home/opam/.opam/5.2',str(B/'XRa_opam')],check=True)
finally:subprocess.run(['docker','rm',cid],check=True)
print('NATIVE_DEPENDENCY_SWITCH_COPIED',image,flush=True)
