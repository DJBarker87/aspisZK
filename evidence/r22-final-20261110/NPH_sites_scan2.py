#!/usr/bin/env python3
"""NPH_ step A (tightened textual screen, lead ruling 2 of 2026-11-10). For each checked field
family (CW, QA, SM, SC, FIq, R72) list EVERY reached definition (def/abbrev/instance, any
namespace, including the family's own namespace and the hand-written wrappers under it such as
AspisR1CurrentWide.Proof.wide_add) whose body names a family definition that reaches one of the
family's domain-only kernels (M31.add/sub/neg, CM31.mul/square). Names are resolved against the
declaring namespace chain and every `open` in the module before the declaration (over-approximate:
an `open` is treated as module-wide from its position). One level of alias is followed: a reached
abbrev/def whose body is a bare reference to such a definition is itself treated as a family
definition. Sources: the replayed L187 src tree (the committed-blob list of L187_CLOSURE.json has several distinct
sources for 122 modules, and the first is not always the replayed one; NPH_sites_scan.py used it); reach: deployed_splitB REACHABLE.
Usage: NPH_sites_scan2.py CONE.json OLD_SITES.json OUT.json SRC_DIR"""
import json,lzma,subprocess,re,sys,collections
EV='/Users/dominic/ZK/.worktrees/cx-r22/evidence/'
C=EV+'replay-l187-20261109/L187_CLOSURE.json.xz'
RE=EV+'replay-l187-20261109/final/L187_AX2_splitB/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz'
cone=json.load(open(sys.argv[1]));old=json.load(open(sys.argv[2]))
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
out={};summ={}
for f,N in FAM.items():
  K=set(KER[f])
  famdefs={x for x in D if x.startswith(N+'.')}
  # family definitions that reach a kernel inside the family (fixpoint), then one alias level outside
  R=set(K)
  while True:
    new={x for x in famdefs if x not in R and refs[x]&R}
    if not new: break
    R|=new
  alias={x for x in D if not x.startswith(N+'.') and refs[x] and refs[x]<=R and len(re.sub(r'\s','',D[x]['body'].split(':=',1)[-1]))<200 and '←' not in D[x]['body'] and ' do' not in D[x]['body']}
  RA=R|alias
  sites=[]
  for x,info in D.items():
    if x in K: continue
    u=sorted(refs[x]&RA)
    if not u: continue
    kind='in_family_extracted' if x.startswith(N+'.') and info['module'].endswith(('.Funs','Funs')) or (x.startswith(N+'.') and info['module'].startswith('RPu_FIq_')) else ('in_family_handwritten' if x.startswith(N+'.') else ('alias' if x in alias else 'outside'))
    sites.append(dict(site=x,decl_kind=info['kind'],module=info['module'],site_class=kind,uses=u,uses_kernel_directly=sorted(refs[x]&K)))
  oldc={y['site']:y.get('covered_by_NPH_step2_or_3',False) for y in old.get(f,[])}
  for y in sites: y['covered_before_this_run']=bool(oldc.get(y['site'],False))
  out[f]=sorted(sites,key=lambda y:(y['site_class'],y['site']))
  summ[f]=dict(domain_kernels=sorted(K),family_defs_reaching_kernels=len(R),aliases=sorted(alias),sites=len(sites),by_class=dict(collections.Counter(y['site_class'] for y in sites)),old_screen_executing=old['_summary'][f]['executing_sites'])
out['_summary']=summ
out['_note']='NPH_sites_scan2 (tightened): textual, name-resolved through namespaces and opens, includes in-family callers and one alias level. A lower bound only for references the regex cannot see (notation, instance resolution, auto-bound names); it is the checklist for judgment (b). covered flags are set per site in NPH_SITES.json by the joins of this run.'
json.dump(out,open(sys.argv[3],'w'),indent=1)
for f,v in summ.items(): print(f,json.dumps(v)[:900])
