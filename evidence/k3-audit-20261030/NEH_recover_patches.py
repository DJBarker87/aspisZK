from NEH_scan import *
# Exact contextual patch replay against retained predecessor snapshots.
# A candidate earns a match only by SHA256 equality to its receipt, never by name.
versions=collections.defaultdict(dict);recovered={};history=[]
d=ROOT/'evidence/native-tx2c-20261027'
patches=sorted(d.glob('*patch'))
for p in patches:
 for n,t in patched_files(p.read_text()):versions[n][sha(t.encode())]=t
for turn in range(3):
 count=0
 for p in patches:
  for n,v in list(versions.items()):
   for h,t in list(v.items()):
    for path,new in patched_files(p.read_text(),{n:t}):
     hh=sha(new.encode())
     if hh not in versions[path]:versions[path][hh]=new;count+=1;history.append(dict(patch=str(p.relative_to(ROOT)),base_path=n,base_sha256=h,path=path,sha256=hh))
 if not count:break
for n,v in versions.items():
 for h,t in v.items():recovered[h+'/'+n]=t
(E/'NEH_RECOVERED_SOURCES.json.xz').write_bytes(lzma.compress(json.dumps(recovered,sort_keys=True).encode()))
(E/'NEH_PATCH_RECOVERY.json').write_text(json.dumps(history,indent=2)+'\n')
print('recovered candidate versions',len(recovered))
for n in [27,28,31]:
 r=json.loads((d/f'NBG_K{n:03}'/'receipt.json').read_text());print(n,[(path,h in versions.get(path.split('_src/')[-1],{})) for path,h in r['source_hashes'].items() if path.endswith('.rs')])
