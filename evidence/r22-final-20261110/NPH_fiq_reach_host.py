#!/usr/bin/env python3
"""NPH_ (R22, FIq): read-only textual FORWARD reachability over reached definition bodies (def/abbrev/
instance; theorems excluded), with the NPH_sites_scan2 name resolution. Roots: every definition of the
extracted adapter program (module AdapterRwModel) and the deployed configuration/program records
(ROOTS, matched by suffix). A site not forward-reachable from the roots through definition bodies is
referenced only from theorems or from definitions that are themselves unreachable: a NOT_EXECUTING
candidate (textual; misses references through notation and implicit instance resolution).
Usage (host, read-only): NPH_fiq_reach_host.py REACHABLE.txt.xz NPH_R22_CONE.json NPH_SITES.json SRC_DIR > OUT.json"""

import json,lzma,subprocess,re,sys,collections
RE=sys.argv[1];cone=json.load(open(sys.argv[2]));sites=json.load(open(sys.argv[3]))
reach=set(lzma.open(RE,'rt').read().split())
import pathlib
SRC=pathlib.Path(sys.argv[4])  # the L187 replay src tree (host codex-cx-replay-l187-20261109/src, or an extract of its l187_src.tar.xz)
src={str(q.relative_to(SRC))[:-5].replace('/','.'):q.read_text(errors='replace') for q in SRC.rglob('*.lean')}
FAM={'CW':'AspisR1CurrentWide','QA':'AspisR1Qm31ArithmeticProbe','SM':'AspisR1SelectedMaskProbe','SC':'AspisR1SemanticCallExtraction','FIq':'FIq_Native','R72':'AspisR72Sampler'}
KER={f:sorted(x['definition'] for x in cone['definitions'] if x['definition'].startswith(N+'.') and x['nph_judgment'].startswith('DOMAIN_LEMMA')) for f,N in FAM.items()}
tok=re.compile(r"(?<![\w.'])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)")
declre=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe|nonrec)\s+)*(def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque|axiom)\s+(\S+)',re.M)
evre=re.compile(r'^(namespace|end|open|section)\b[ \t]*(.*)$',re.M)
D={}  # full name -> dict
for mod,t in src.items():
  evs=sorted([(m.start(),'ev',m.group(1),m.group(2).strip()) for m in evre.finditer(t)]+[(m.start(),'decl',m.group(1),m.group(2)) for m in declre.finditer(t)])
  stack=[];opens=[];decls=[]
  for pos,typ,k,a in evs:
    if typ=='ev':
      if k=='namespace': stack.append(('ns',a.split()[0] if a else ''))
      elif k=='section': stack.append(('sec',a))
      elif k=='end':
        if stack: stack.pop()
      elif k=='open':
        a=re.sub(r'\bin\b.*','',a);a=re.sub(r'\(.*?\)|hiding.*|renaming.*','',a)
        opens+=[x for x in a.split() if re.match(r'[A-Za-z_]',x)]
    else:
      ns='.'.join(x[1] for x in stack if x[0]=='ns' and x[1])
      decls.append((pos,k,a,ns,list(opens)))
  for j,(pos,k,n,ns,op) in enumerate(decls):
    if k in ('theorem','lemma','structure','inductive','class','axiom'): continue
    end=decls[j+1][0] if j+1<len(decls) else len(t)
    # stop body at the next namespace/end/open event
    nxt=[m.start() for m in evre.finditer(t,pos+1,end)];end=min([end]+nxt)
    n=n.lstrip('_root_.') if n.startswith('_root_.') else n
    full=(ns+'.'+n) if ns else n
    if full in reach: D[full]=dict(module=mod,kind=k,body=t[pos:end],ns=ns,opens=op)
def resolve(name,info):
  pre=info['ns'].split('.') if info['ns'] else []
  cands=[name]+['.'.join(pre[:i])+'.'+name for i in range(len(pre),0,-1)]+[o+'.'+name for o in info['opens']]+[a+'.'+o+'.'+name for o in info['opens'] for a in ['AspisR1'] ]
  return [c for c in cands if c in D]
refs={}
for full,info in D.items():
  body=info['body'].split(':=',1)[1] if ':=' in info['body'] else info['body']
  body=re.sub(r'--[^\n]*|/-.*?-/','',body,flags=re.S)
  s=set()
  for m in tok.finditer(body):
    for c in resolve(m.group(1),info):
      if c!=full: s.add(c)
  refs[full]=s

ROOTS=['NNH_CorrectConfiguration.sdk','NNH_CorrectConfiguration.configuration','NNH_HostCtx.sdk','NNH_HostCtx.configuration',
 'DrvC_Installation.sdk','DrvC_Installation.currentInstalled','DrvC_Installation.stage','CPH_Program.verifier','ARW_Induced.program',
 'ARX_AdmittedRuntime.runtime','NOC_HostSeed.m0','NNH_HostSeed.m0','IDa_Deployed.deployedConfiguration','IDa_Deployed.boundaries']
roots=sorted({x for x in D if D[x]['module']=='AdapterRwModel'}|{x for x in D for r in ROOTS if x==r or x.endswith('.'+r)})
seen=set(roots);todo=list(roots)
while todo:
  x=todo.pop()
  for y in refs.get(x,()):
    if y not in seen: seen.add(y);todo.append(y)
res={}
for f in ['FIq','QA','SM','CW','SC','R72']:
  L=sites.get(f,[])
  res[f]=dict(total=len(L),forward_reachable=sorted(e['site'] for e in L if e['site'] in seen),
    not_forward_reachable=sorted(e['site'] for e in L if e['site'] not in seen))
fq=[x for x in seen if x.startswith('FIq_Native.')]
print(json.dumps(dict(note=__doc__.strip().splitlines()[0],roots_matched=[r for r in ROOTS if any(x==r or x.endswith('.'+r) for x in roots)],
  n_roots=len(roots),n_forward=len(seen),n_defs=len(D),FIq_Native_forward=len(fq),FIq_Native_forward_names=sorted(fq),families=res),indent=1))
