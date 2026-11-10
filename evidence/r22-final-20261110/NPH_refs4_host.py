#!/usr/bin/env python3
"""NPH_ (R22, item 2 loop/decoder screen, BACKWARD): the NPH_fiq_refs_host.py referrer screen (same parser, name
resolution, ROOTS, TIE_WORDS and classification, copied unchanged) run on arbitrary targets with a per-target STOP set.
A STOP node is a definition proved ok on its whole reached domain (a TOTAL entry or a composed site); the walk does not
pass it. Classes as in NPH_fiq_refs_host.py (COVERED_BY_TERMINAL here means: every upward path from the target meets one
of its STOP nodes, and the remaining tops are theorem-only without tie candidate).
Usage (host, read-only): NPH_refs4_host.py SRC_DIR SPEC.json > OUT.json
SPEC: {"targets": {"<def>": ["<stop def>", ...], ...}, "controls": ["<def known to execute>", ...]}
Textual screen: references made only through notation or instance resolution are not seen; flagged for lead review."""
import json,re,sys,pathlib,collections
SRC=pathlib.Path(sys.argv[1]);spec=json.load(open(sys.argv[2]))
src={str(q.relative_to(SRC))[:-5].replace('/','.'):q.read_text(errors='replace') for q in SRC.rglob('*.lean')}
tok=re.compile(r"(?<![\w.'])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)")
declre=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|unsafe|nonrec)\s+)*(def|theorem|lemma|abbrev|instance|structure|inductive|class|opaque|axiom|example)\s+(\S+)',re.M)
evre=re.compile(r'^(namespace|end|open|section)\b[ \t]*(.*)$',re.M)
DEFK={'def','abbrev','instance','opaque'}
D={};order=[]
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
    end=decls[j+1][0] if j+1<len(decls) else len(t)
    nxt=[m.start() for m in evre.finditer(t,pos+1,end)];end=min([end]+nxt)
    n=n[len('_root_.'):] if n.startswith('_root_.') else n
    full=(ns+'.'+n) if ns else n
    if k=='example': full='example@%s:%d'%(mod,pos)
    key=full if full not in D else full+'@'+mod
    D[key]=dict(name=full,module=mod,kind=k,text=t[pos:end],ns=ns,opens=op)
names=collections.defaultdict(list)
for key,v in D.items(): names[v['name']].append(key)
def resolve(name,info):
  pre=info['ns'].split('.') if info['ns'] else []
  cands=[name]+['.'.join(pre[:i])+'.'+name for i in range(len(pre),0,-1)]+[o+'.'+name for o in info['opens']]+['AspisR1.'+o+'.'+name for o in info['opens']]
  return [c for c in cands if c in names]
rev=collections.defaultdict(set)
for key,info in D.items():
  body=re.sub(r'--[^\n]*|/-.*?-/','',info['text'],flags=re.S)
  first=True
  for m in tok.finditer(body):
    if first: first=False;continue  # the declared name itself
    for c in resolve(m.group(1),info):
      if c!=info['name']: rev[c].add(key)
STOP=set()
ROOTS=['NNH_CorrectConfiguration.sdk','NNH_CorrectConfiguration.configuration','NNH_HostCtx.sdk','NNH_HostCtx.configuration',
 'DrvC_Installation.sdk','DrvC_Installation.currentInstalled','DrvC_Installation.stage','CPH_Program.verifier','ARW_Induced.program',
 'ARX_AdmittedRuntime.runtime','NOC_HostSeed.m0','NNH_HostSeed.m0','IDa_Deployed.deployedConfiguration','IDa_Deployed.boundaries',
 'NOC_Stage1Forward.S','NNH_Run5bCurrentShape.current','VTop_Stages','TAS_FinalB']
TIE_WORDS=['IDa_Deployed','DrvC_Installation','NNH_HostCtx','NNH_CorrectConfiguration','NOC_Stage1Forward','currentInstalled','NNH_Run5bCurrentShape','AdapterRw','VTop_','TAS_Final','NOC_Op9Slot','deployed','NNH_','NOC_','NHW_','NNG_','LIB_','Stage1','Run6','Run5','Host','VTop','Tx1','Tx2','adapter','Adapter']
def isroot(n):
  return any(D[k]['module']=='AdapterRwModel' for k in names.get(n,[])) or any(n==r or n.endswith('.'+r) or n.startswith(r+'.') for r in ROOTS)
cache={}
def classify(s):
  seen={s};todo=[s];hit=False;tops=[];roots=[]
  while todo:
    x=todo.pop()
    if isroot(x): roots.append(x)
    drefs=sorted({D[k]['name'] for k in rev.get(x,()) if D[k]['kind'] in DEFK}-{x})
    up=[y for y in drefs if y not in STOP]
    if len(up)<len(drefs): hit=True
    if not drefs: tops.append(x)
    for y in up:
      if y not in seen: seen.add(y);todo.append(y)
  topinfo=[]
  for x in tops:
    th=sorted({D[k]['name']+' ['+D[k]['module']+']' for k in rev.get(x,()) if D[k]['kind'] not in DEFK})
    tie=[y for y in th if any(w in y for w in TIE_WORDS)]
    topinfo.append(dict(top=x,root=isroot(x),theorem_referrers=len(th),theorem_referrers_sample=th[:6],tie_candidates=tie[:6]))
  if roots: cls='REACHES_ROOT_OUTSIDE_TERMINAL'
  elif any(t['tie_candidates'] for t in topinfo): cls='TIE_CANDIDATE'
  else: cls='COVERED_BY_TERMINAL' if hit else 'PROOF_ONLY'
  return dict(cls=cls,meets_stop=hit,upward_defs=len(seen),roots=sorted(set(roots))[:10],tops=topinfo)
out=[];cnt=collections.Counter()
for s,stops in spec['targets'].items():
  STOP.clear();STOP.update(stops)
  r=classify(s) if s in names else dict(cls='UNKNOWN_NAME')
  r['direct_def_referrers']=sorted({D[k]['name'] for k in rev.get(s,()) if D[k]['kind'] in DEFK})
  r['stop']=sorted(stops);cnt[r['cls']]+=1;out.append(dict(target=s,**r))
STOP.clear()
controls=[dict(control=c,known=c in names,**(classify(c) if c in names else {})) for c in spec.get('controls',[])]
json.dump(dict(note=__doc__.strip().splitlines()[0],n_decls=len(D),counts=dict(cnt),roots=ROOTS,tie_words=TIE_WORDS,controls=controls,targets=out),sys.stdout,indent=1)
