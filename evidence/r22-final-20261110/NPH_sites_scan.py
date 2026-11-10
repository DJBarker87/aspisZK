#!/usr/bin/env python3
"""NPH_ step 3 (textual screen): reached call sites of the checked field families. For each
family namespace (CW, QA, SM, SC, FIq, R72), list every reached DEFINITION outside that
family's own `field.` namespace whose body names a `<NS>.field.` function, with the names it
uses. Sources: L187_CLOSURE.json git blobs; reach: deployed_splitB REACHABLE. Usage: NPH_sites_scan.py OUT.json"""
import json,lzma,subprocess,re,sys
C='/Users/dominic/ZK/.worktrees/cx-r22/evidence/replay-l187-20261109/L187_CLOSURE.json.xz'
RE='/Users/dominic/ZK/.worktrees/cx-r22/evidence/replay-l187-20261109/final/L187_AX2_splitB/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz'
d=json.loads(lzma.decompress(open(C,'rb').read()));reach=set(lzma.open(RE,'rt').read().split())
FAM={'CW':'AspisR1CurrentWide','QA':'AspisR1Qm31ArithmeticProbe','SM':'AspisR1SelectedMaskProbe','SC':'AspisR1SemanticCallExtraction','FIq':'FIq_Native','R72':'AspisR72Sampler'}
declre=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*(def|theorem|lemma|abbrev|instance|structure)\s+(\S+)',re.M)
out={k:[] for k in FAM}
for m in d['modules']:
  for c in m.get('committed_sources',[])[:1]:
    t=subprocess.run(['git','-C','/Users/dominic/ZK','cat-file','-p',c['git_blob']],capture_output=True,text=True).stdout
    if not any(ns in t for ns in FAM.values()): continue
    nss=[(x.start(),x.group(1)) for x in re.finditer(r'^namespace\s+(\S+)',t,re.M)]
    starts=[(x.start(),x.group(1),x.group(2)) for x in declre.finditer(t)]
    for i,(s,k,n) in enumerate(starts):
      if k in ('theorem','lemma','structure'): continue
      e=starts[i+1][0] if i+1<len(starts) else len(t);body=t[s:e]
      ns=[x for x in nss if x[0]<s];ns=ns[-1][1] if ns else ''
      full=ns+'.'+n if ns else n
      if full not in reach: continue
      for f,N in FAM.items():
        if full.startswith(N+'.'): continue
        used=sorted(set(re.findall(re.escape(N)+r'\.(?:aspis_core\.)?field\.[\w.]+',body)))
        if used: out[f].append(dict(site=full,kind=k,module=m['module'],uses=used))
json.dump(out,open(sys.argv[1],'w'),indent=1)
for f,v in out.items(): print(f,len(v),sorted(x['site'] for x in v)[:60])
