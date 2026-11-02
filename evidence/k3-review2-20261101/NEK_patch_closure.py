"""Recover content-pinned sources through strict historical patch chains."""
from NEK_scan import *
import sys,lzma

def chain(directory,target,rounds=4):
 variants={}
 b=frozen(target)
 if b:variants[sha(b)]=b.decode()
 patches=[]
 for p in sorted((ROOT/directory).glob('*.patch')):
  text=p.read_text()
  if ('+++ b/'+target+'\n') not in text:continue
  patches.append((str(p.relative_to(ROOT)),text))
  for n,t in patched_files(text):
   if n==target:variants[sha(t.encode())]=t
 paths=[]
 for step in range(rounds):
  added={}
  for origin,text in patches:
   for h,b in list(variants.items()):
    for n,t in patched_files(text,{target:b}):
     if n==target and sha(t.encode()) not in variants:
      key=sha(t.encode());added[key]=t;paths.append(dict(output_sha256=key,base_sha256=h,patch=origin,patch_sha256=sha(text.encode())))
  variants.update(added)
  print(directory,step,len(variants),flush=True)
  if not added:break
 (E/('NEK_'+Path(target).name+'_variants.json.xz')).write_bytes(lzma.compress(json.dumps(variants,sort_keys=True).encode()))
 (E/('NEK_'+Path(target).name+'_patch_chain.json')).write_text(json.dumps(paths,indent=2)+'\n')
 return variants
if __name__=='__main__':chain(*sys.argv[1:])
