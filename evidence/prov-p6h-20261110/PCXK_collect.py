#!/usr/bin/env python3
"""PCXK_collect.py (python3 -I -B): per-file results from the PCXK_L*/receipt.json, failing theorems (error line -> enclosing theorem), affected gate definitions
(statement shape `theorem N : @FRESH = @GATE` + gate module from the file's imports, or PCXH_CREDITED_NAMES), first-crediting job per definition.
Writes PCXK_RESULTS.json and PCXK_FAILED.json."""
import json,glob,os,re,subprocess,collections,lzma
here=os.path.dirname(os.path.abspath(__file__)); os.chdir(here)
def git(*a):
    r=subprocess.run(['git']+list(a),capture_output=True,cwd=here); return r.stdout.decode() if r.returncode==0 else ''
STD={'propext','Classical.choice','Quot.sound'}
files={f['copy']:f for f in json.load(open('PCXK_FILES.json'))['files']}
res={}
for rc in sorted(glob.glob('PCXK_L*/receipt.json')):
    r=json.load(open(rc))
    for s in r['steps']:
        ax=[]; ok=True
        lp=os.path.join(r['attempt'],s['module'],'stdout.log')
        log=open(lp).read() if os.path.exists(lp) else lzma.open(lp+'.xz').read().decode()   # parsed from the full log: the host regex drops names ending in a prime
        for m in re.finditer(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log,re.M):
            a={x.strip() for x in (m.group(2) or '').replace('\n',' ').split(',') if x.strip()}
            ax.append(dict(name=m.group(1),axioms=sorted(a))); ok&=a<=STD
        copy='PCXK_sources/'+s['module']+'.lean'
        res[copy]=dict(attempt=r['attempt'],exit_status=s['exit_status'],wall_seconds=round(s['wall_seconds'],1),peak_rss_kib=s['peak_rss_kib'],swaps=s['swaps'],errors=s['errors'],
            heartbeat_errors=s['heartbeat_errors'],print_axioms_lines=len(ax),axioms_standard_only=ok,sorry_axiom=any('sorryAx' in x['axioms'] for x in ax),theorems_expected=files[copy]['theorems'],error_lines=s['error_lines'])
THM=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\s+(\S+)')
CR=re.compile(r'^theorem\s+(\S+)\s*:\s*@(\S+)\s*=\s*@(\S+)\s*:=',re.M)
pv=json.loads(git('show','research:evidence/prov-p6w-20261110/PCXH_PROVENANCE.json'))['per_definition_class']
byname=collections.defaultdict(list)
for k in pv: m,d=k.split('|',1); byname[d].append(m)
names={r['credited_name']:r for r in json.loads(git('show','research:evidence/prov-p6w-20261110/PCXH_CREDITED_NAMES.json'))['records']}
def jobinfo(d):
    p=[x for x in git('ls-tree','--name-only','research','evidence/'+d+'/').split('\n') if x.endswith('_ATTEMPTS.jsonl')]
    if not p: return None,None
    t=git('log','--diff-filter=A','--format=%ct','research','--',p[0]).strip().split('\n')[-1]
    return os.path.basename(p[0])[:-len('_ATTEMPTS.jsonl')],int(t or 0)
failed=[]
for copy,r in res.items():
    if r['exit_status']==0: continue
    src=open(copy).read().split('\n')
    for e in r['error_lines']:
        m=re.search(r'\.lean:(\d+):(\d+): error: (.*)',e)
        if not m: continue
        ln=int(m.group(1)); th=None
        for i in range(ln-1,-1,-1):
            d=THM.match(src[i])
            if d: th=d.group(1); break
        failed.append(dict(copy=copy,original=files[copy]['original'],line=ln,theorem=th,message=m.group(3)[:300]))
out=dict(schema='PCXK_FAILED/1',target_established=False,failed_theorems=failed,definitions=[])
# first-crediting job per definition over ALL 78 originals (a definition is demoted only if every crediting theorem failed)
cred=collections.defaultdict(list)
for copy,f in files.items():
    s=open(copy).read(); imps=re.findall(r'^import\s+(\S+)',s,re.M); gm=[i for i in imps if i!='Aeneas']
    d=f['original'].split('/')[1]; pre,t=jobinfo(d)
    for m in CR.finditer(s):
        n,fr,g=m.groups(); c=byname.get(g,[])
        if len(c)>1: c=[x for x in c if x in gm] or c
        if len(c)==1: cred[f'{c[0]}|{g}'].append(dict(theorem=n,copy=copy,job=pre,evidence_dir='evidence/'+d,job_time=t))
failset={(x['copy'],x['theorem']) for x in failed}
for k,v in sorted(cred.items()):
    bad=[x for x in v if (x['copy'],x['theorem'].split('.')[-1]) in failset or any(x['copy']==c and x['theorem'].endswith('.'+t) for c,t in failset if t)]
    if bad:
        first=min(v,key=lambda x:x['job_time'] or 0)
        out['definitions'].append(dict(definition=k,failing=bad,all_crediting=v,first_crediting_job=dict(prefix=first['job'],evidence_dir=first['evidence_dir']),demote=len(bad)==len(v)))
# owner decision 2026-11-10: row ReviewedTranscription-PublicPreparation.public_bytes withdrawn -> every definition credited through it (PCXF_TRUST_NAMING / PCXF_ALL_STATUS trust_rows, NPL_PublicBytes evidence) goes to OPEN
tw=[]; seen=set()
def walk(x):
    if isinstance(x,dict):
        tr=x.get('trust_rows')
        if tr and any('ReviewedTranscription-PublicPreparation' in t for t in tr) and x.get('module') and x.get('definition'):
            k=x['module']+'|'+x['definition']
            if k not in seen: seen.add(k); tw.append(dict(key=k,previous_class=x.get('status') or 'DEPENDS_ON_LIBRARY_TRUST',theorem=x.get('theorem'),in_splitB_cone=x.get('in_splitB_cone'),in_baseline_universe=k in pv,trust_rows=tr))
        for v in x.values(): walk(v)
    elif isinstance(x,list):
        for v in x: walk(v)
for f in ('prov-p6u-20261110/PCXF_TRUST_NAMING.json','prov-p6u-20261110/PCXF_ALL_STATUS.json'): walk(json.loads(git('show','research:evidence/'+f)))
out['trust_row_withdrawn']=dict(cause='owner decision 2026-11-10: transcription row withdrawn',row='ReviewedTranscription-PublicPreparation.public_bytes',evidence='evidence/public-bytes-20261110 (NPL_PublicBytes.gate_eq, gate_total_length)',
    method='definitions whose trust_rows name the row, read from PCXF_TRUST_NAMING.json and PCXF_ALL_STATUS.json; ReviewedTranscription-FieldDerives untouched (std derive expansions)',definitions=tw,demoted_to='OPEN')
json.dump(dict(schema='PCXK_RESULTS/1',target_established=False,files=res),open('PCXK_RESULTS.json','w'),indent=1)
json.dump(out,open('PCXK_FAILED.json','w'),indent=1)
n0=sum(1 for r in res.values() if r['exit_status']==0)
print('files',len(res),'exit0',n0,'failed theorems',len(failed),'definitions affected',len(out['definitions']),'demote',sum(d['demote'] for d in out['definitions']))
