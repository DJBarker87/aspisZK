"""Reconstruct compiled scratch sources from frozen git blobs and exact patches.
This is an additional independent check; no source or inherited gate is edited.
"""
from pathlib import Path
import subprocess,hashlib,json,re,sys
from functools import lru_cache
E=Path(__file__).resolve().parent.parent/'pool-b3-20261106';REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
sha=lambda b:hashlib.sha256(b).hexdigest()
@lru_cache(maxsize=1)
def frozen():
 pins=json.loads((E.parent/'extract-stage-20261106/NHR_STAGING_MANIFEST.json').read_text())['files']
 tree={line.split('\t',1)[1]:line.split()[2] for line in subprocess.check_output(['git','ls-tree','-r',REV],text=True).splitlines()}
 assert all(tree[n]==pin['git_blob'] for n,pin in pins.items())
 blobs=list(dict.fromkeys(p['git_blob'] for p in pins.values()))
 raw=subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(blobs)+'\n').encode());pos=0;data={}
 for blob in blobs:
  end=raw.index(b'\n',pos);header=raw[pos:end].split();assert header[0].decode()==blob and header[1]==b'blob'
  size=int(header[2]);start=end+1;data[blob]=raw[start:start+size];pos=start+size+1
 return {n:data[p['git_blob']] for n,p in pins.items()}
def apply(files,text):
 lines=text.splitlines(keepends=True);i=0
 while i<len(lines):
  if not lines[i].startswith('--- '):i+=1;continue
  old=lines[i][4:].strip();new=lines[i+1][4:].strip();assert lines[i+1].startswith('+++ ');i+=2
  path=new.removeprefix('b/');before=[] if old=='/dev/null' else files[old.removeprefix('a/')].decode().splitlines(keepends=True)
  after=[];cursor=0
  while i<len(lines) and not lines[i].startswith(('--- ','diff --git ')):
   if not lines[i].startswith('@@ '):i+=1;continue
   h=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i]);assert h
   start=int(h[1])-1 if int(h[1]) else 0;assert start>=cursor
   after+=before[cursor:start];cursor=start;i+=1
   while i<len(lines) and not lines[i].startswith(('@@ ','--- ','diff --git ')):
    line=lines[i]
    if line.startswith(' '):assert before[cursor]==line[1:],(path,cursor);after.append(line[1:]);cursor+=1
    elif line.startswith('-'):assert before[cursor]==line[1:],(path,cursor);cursor+=1
    elif line.startswith('+'):after.append(line[1:])
    elif line.startswith('\\ No newline'):raise AssertionError('Unsupported non-newline patch')
    else:break
    i+=1
  after+=before[cursor:];files[path]=''.join(after).encode()
 return files
def check(a,base=None):
 files=dict(frozen() if base is None else base)
 for patch in [subprocess.check_output(['git','show','HEAD:evidence/kani-mitig-20261028/KMX_copy_stubs.patch'],text=True),(E/'NFD_contract_controls.patch').read_text(),(E/(a+'-NFD_oracle.patch')).read_text(),(E/(a+'-NFD_native_contracts.patch')).read_text()]:apply(files,patch)
 actual=json.loads((E/(a+'-RUST_SHA256.json')).read_text())
 errors=[name for name,data in files.items() if actual.get(name)!=sha(data)]
 extras=sorted(set(actual)-set(files));unexpected=[n for n in extras if n.startswith(('crates/','programs/'))]
 assert not errors and not unexpected,(errors,unexpected)
 return dict(attempt=a,frozen_revision=REV,exact_frozen_plus_patches=True,checked_files=len(files),inert_seed_extras=extras,errors=errors,unexpected_compiled_paths=unexpected)
if __name__=='__main__':
 base=frozen();results=[]
 for a in sys.argv[1:]:
  result=check(a,base);(E/(a+'-frozen-identity.json')).write_text(json.dumps(result,indent=1)+'\n');results.append(result)
 print(json.dumps(dict(attempts=len(results),all_exact=True)))
