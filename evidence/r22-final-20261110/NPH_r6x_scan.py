#!/usr/bin/env python3
"""NPH_ step 1 (textual screen): every declaration in the L187 closure sources (git blobs of
L187_CLOSURE.json) whose body names AspisR65Field/AspisR66Field field.M31.add/sub/neg, with kind
and membership in the deployed_splitB REACHABLE list. Usage: NPH_r6x_scan.py OUT.json"""
import json,lzma,subprocess,re,sys
C='/Users/dominic/ZK/.worktrees/cx-r22/evidence/replay-l187-20261109/L187_CLOSURE.json.xz'
d=json.loads(lzma.decompress(open(C,'rb').read()))
reach=set(lzma.open('/Users/dominic/ZK/.worktrees/cx-r22/evidence/replay-l187-20261109/final/L187_AX2_splitB/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz','rt').read().split())
paths=[]
for m in d['modules']:
  for c in m.get('committed_sources',[]): paths.append((m['module'],c['path'],c['git_blob']))
hits=[]
declre=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*(def|theorem|lemma|abbrev|instance|structure|example)\s+(\S+)',re.M)
for mod,p,blob in paths:
  t=subprocess.run(['git','-C','/Users/dominic/ZK','cat-file','-p',blob],capture_output=True,text=True).stdout
  if 'AspisR65Field' not in t and 'AspisR66Field' not in t: continue
  nss=[(m.start(),m.group(1)) for m in re.finditer(r'^namespace\s+(\S+)',t,re.M)]
  opens=re.findall(r'^open .*',t,re.M)
  starts=[(m.start(),m.group(1),m.group(2)) for m in declre.finditer(t)]
  for i,(s,k,n) in enumerate(starts):
    e=starts[i+1][0] if i+1<len(starts) else len(t)
    body=t[s:e]
    ns=[x for x in nss if x[0]<s]; ns=ns[-1][1] if ns else ''
    full=ns+'.'+n if ns else n
    for fam in ['AspisR65Field','AspisR66Field']:
      for op in ['add','sub','neg']:
        pat=r'(?<![\w.])(?:'+fam+r'\.)?field\.M31\.'+op+r'\b'
        if re.search(pat,body) and (fam in body or fam==ns or any(fam in o for o in opens)):
          if full==fam+'.field.M31.'+op: continue
          hits.append(dict(module=mod,path=p,decl=full,kind=k,family=fam,op=op,in_reach=full in reach))
json.dump(hits,open(sys.argv[1],'w'),indent=1)
seen=set()
for h in hits:
  key=(h['decl'],h['kind'],h['family'],h['op'],h['in_reach'],h['module'])
  if key in seen: continue
  seen.add(key);print(*key)
