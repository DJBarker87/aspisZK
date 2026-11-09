#!/usr/bin/env python3
"""Locate, for each stale dependency version (dep, pinned sha256), an existing host file with exactly
that hash (the pinned path, else any indexed copy with the module's relative path); write a compare tsv."""
import json,sys,hashlib,os,collections
W='/home/dombarker/project-offloads/codex-cx-replay-l187-20261109'
q=json.load(sys.stdin)
byname=collections.defaultdict(list)
for line in open(W+'/all_oleans.txt'):
  p=line.rstrip('\n'); byname[os.path.basename(p)].append(p)
def h(p):
  try: return hashlib.sha256(open(p,'rb').read()).hexdigest()
  except Exception: return None
rows=[];tsv=[]
for i,x in enumerate(q):
  found=x['pinned_path'] if h(x['pinned_path'])==x['pinned_sha'] else None
  if not found:
    rel=x['dep'].replace('.','/')+'.olean'
    for p in byname.get(os.path.basename(rel),[]):
      if p.endswith('/'+rel) and h(p)==x['pinned_sha']: found=p; break
  rows.append(dict(x,pinned_file_found=found))
  if found: tsv.append('%d\t%s\t%s\n'%(i,found,x['closure']))
json.dump(rows,open(W+'/tools/stage4_located.json','w')); open(W+'/tools/stage4.tsv','w').write(''.join(tsv))
print(len(rows),'versions;',len(tsv),'located')
