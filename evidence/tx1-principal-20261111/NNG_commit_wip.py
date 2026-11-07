"""Preserve only this lane's WIP when ENOSPC prevents rewriting its270MiB index."""
from pathlib import Path
import subprocess,os,json
PREFIX="evidence/tx1-principal-20261111/"
def git(*args,data=None):
 r=subprocess.run(["git",*args],input=data,capture_output=True,check=True)
 return r.stdout
old=git("rev-parse","HEAD").decode().strip()
branch=git("symbolic-ref","HEAD").decode().strip()
assert branch=="refs/heads/codex/cx-tx1-principal-20261107"
staged=git("diff","--cached","--name-only","-z").decode().split("\0")
assert all(not n or n.startswith(PREFIX) for n in staged)
paths=set(git("diff","--name-only","-z",old,"--",PREFIX).decode().split("\0"))
paths.update(git("ls-files","--others","--exclude-standard","-z","--",PREFIX).decode().split("\0"))
paths.discard("")
assert paths and all(n.startswith(PREFIX)for n in paths)
trie={}
for path in sorted(paths):
 p=Path(path)
 assert not p.is_file()or p.stat().st_size<=20_000_000,path
 node=trie
 for part in path.split("/"):node=node.setdefault(part,{})
 node[None]=path
def tree(base,node):
 entries={}
 if base:
  for raw in git("ls-tree","-z",base).split(b"\0"):
   if not raw:continue
   left,name=raw.split(b"\t",1);mode,typ,oid=left.decode().split()
   entries[name.decode()]=(mode,typ,oid)
 for name,child in node.items():
  assert name is not None
  if None in child:
   assert len(child)==1
   p=Path(child[None])
   if not p.exists():entries.pop(name,None);continue
   assert p.is_file()and not p.is_symlink()
   oid=git("hash-object","-w","--stdin",data=p.read_bytes()).decode().strip()
   mode="100755"if p.stat().st_mode&0o111 else"100644"
   entries[name]=(mode,"blob",oid)
  else:
   prior=entries.get(name)
   assert prior is None or prior[1]=="tree"
   oid=tree(prior[2]if prior else None,child)
   entries[name]=("040000","tree",oid)
 payload=b"".join((mode+" "+typ+" "+oid+"\t"+name+"\0").encode()for name,(mode,typ,oid)in sorted(entries.items()))
 return git("mktree","-z",data=payload).decode().strip()
root=tree(git("rev-parse",old+"^{tree}").decode().strip(),trie)
commit=git("commit-tree",root,"-p",old,data=b"Record TX1 137 fold WIP and mandatory local disk stop\n").decode().strip()
changed=git("diff-tree","--no-commit-id","--name-only","-r",old,commit).decode().splitlines()
assert changed and all(n.startswith(PREFIX)for n in changed)
git("update-ref",branch,commit,old)
print(json.dumps({"commit":commit,"parent":old,"paths":len(changed),"outside_own_prefix":False,"index":"unchanged due ENOSPC; refresh after freeing disk","no_push":True}))
