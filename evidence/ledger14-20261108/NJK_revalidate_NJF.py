"""Read-only gate validation. Only NJF_VALIDATION.json is written in this directory."""
from pathlib import Path
import json,re,hashlib,lzma,copy
E=Path('/Users/dominic/ZK/.worktrees/cx-ledger14/evidence/slice-d-pair8-20261107')
B='/home/dombarker/project-offloads/codex-cx-slice-d-pair8-20261107'
sha=lambda x:hashlib.sha256(x).hexdigest()
def require(v,msg):
 if not v:raise ValueError(msg)
def j(p):return json.loads(p.read_text())
records=[json.loads(x)for x in(E/'NJF_ATTEMPTS.jsonl').read_text().splitlines()]
R={r['attempt']:r for r in records};require(len(R)==len(records),'duplicate attempt')
for prefix,limit in [('K',60),('L',120)]:
 ids=sorted(int(a[-3:])for a in R if a.startswith('NJF_'+prefix))
 require(ids==list(range(1,len(ids)+1)) and len(ids)<=limit,'budget/ID continuity')
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def scope(r):
 require(r['limits']==limits,'limits')
 require(str(r['swaps'])=='0','swap')
 require(r['env']['CARGO_TARGET_DIR']==B+'/NJF_target','private target')
 require(r.get('source_revision') and r.get('source_hashes'),'source pins')
 require(r['wall_seconds']>0 and int(r['peak_rss_kib'])>0,'resource receipt')
for a,r in R.items():
 scope(r);ad=j(E/(a+'-admission.json'))
 require(ad['exit']==0 and ad['reservation']['allowed'] is True,'admission')
 if r['kind']=='kani':
  g=j(E/(a+'-graph-check.json'));lock=j(E/(a+'-lock-check.json'));src=j(E/(a+'-source-check.json'))
  require(g['graph_matches_frozen'] and not g['edge_errors'] and not src['errors'],'frozen graph/source')
  require(lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','lock')
  require(r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3','offline/optimized')
  require('--harness-timeout' in r['native_command'] and r['native_command'][r['native_command'].index('--harness-timeout')+1]=='90s','timeout')
  require(r['module']=='weights::NJF_boundary::slice_boundary','no rename')
  index=j(E/a/'SOURCE_INDEX.json')
  for name,p in index.items():
   data=lzma.decompress((E/p['payload']).read_bytes())
   require(sha(data)==p['sha256'] and len(data)==p['bytes'],'packed source')

def source(n):
 a=f'NJF_K{n:03}';index=j(E/a/'SOURCE_INDEX.json');p=index['NJF_src/crates/aspis-r1-cost-probe/src/NJF_boundary.rs']
 return lzma.decompress((E/p['payload']).read_bytes()).decode()
def body(s,name):
 pos=s.index('fn '+name+'(');start=s.index('{',pos);level=1;k=start+1
 while level:
  level+=(s[k]=='{')-(s[k]=='}');k+=1
 return re.sub(r'\s+','',s[pos:k])
# Projections of one universally quantified parent stage. Oracle setup can be
# array- or Vec-backed; both cover every length64 decoded payload (ScratchCarrier).
reference=source(12)
for n in [6,7,8,9,12,14,18,22,23,30,31,32,33,34,35,36,37,38,40,42,43]:
 s=source(n)
 for name in ['regular','common','partial','high','boundary']:
  require(body(s,name)==body(reference,name),'parent/oracle body drift '+str((n,name)))
 require('static mut' not in s and 'stub_verified' not in s and 'proof_for_contract' not in s,'forbidden harness state/contract')

pairs=[('args',12,38,'l.ap0[power]'),('control',14,15,'l.events[0]'),
 ('scratch',6,7,'qw(scratch[index])'),('parts',8,9,'parts[slot].to_limbs()'),
 ('common/partial',42,43,'!same'),('high args',18,40,'l.high_ap0.to_limbs()'),
 ('high value',22,23,'l.high_partial.to_limbs()'),('high pre 3..6',30,31,'l.high_before.to_limbs()'),
 ('high pre 0',32,33,'l.high_before.to_limbs()'),('high pre 1',34,35,'l.high_before.to_limbs()'),('high pre 2',36,37,'l.high_before.to_limbs()')]
def negative(r,s,fragment):
 require(r['exit_status']!=0 and 'timed out' not in s and 'Failed Checks:' in s,'not a semantic control failure')
 require(fragment in s.split('Failed Checks:',1)[1],'control did not fail target data property')
for name,p,n,fragment in pairs:
 a=f'NJF_K{p:03}';b=f'NJF_K{n:03}';sp=(E/a/'stdout.log').read_text();sn=(E/b/'stdout.log').read_text()
 require(R[a]['exit_status']==0 and '1 successfully verified harnesses, 0 failures' in sp,'positive '+a)
 negative(R[b],sn,fragment)
 require(j(E/(a+'-graph-check.json'))['selected_closure']==j(E/(b+'-graph-check.json'))['selected_closure'],'feature graph differs')

semantic=[p for p in E.glob('NJF_*.lean')if p.stem not in ['NJF_Driver','NJF_ProofDriver','NJF_COMBINED_IMPORT']]
lean=[]
for p in sorted(semantic):
 s=p.read_text();require(not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',s,re.M),'forbidden proof '+p.name)
 matches=[r for r in records if r['kind']=='lean' and r['module']==p.stem and r['exit_status']==0 and r['source_hashes'].get('NJF_generated/'+p.name)==sha(p.read_bytes())]
 require(matches,'no passing final source '+p.name)
 r=matches[-1];require(all('sorryAx' not in x for x in r['print_axioms']),'failed source axiom')
 lean.append(dict(module=p.stem,attempt=r['attempt'],sha256=sha(p.read_bytes()),axioms=r['print_axioms']))

final=j(E/'NJF_L044/audit_outputs/RESULT.json');require(final['status']=='PASS' and final['standard_only'] and final['commands']['scan']['exit']==0,'final combined gate')
raw=[json.loads(x[11:])for x in(E/'NJF_L044/audit_outputs/raw.log').read_text().splitlines()if x.startswith('NEP_RESULT ')]
roots=[v for g in j(E/'NJF_AUDIT_ROOTS.json')['groups']for v in g]
require(len(raw)==len(roots) and {r['root']for r in raw}==set(roots),'raw root coverage')
require(all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw),'raw axioms')
scan=[json.loads(x)for x in(E/'NJF_L044/audit_outputs/NJF_LOADED_scan.jsonl').read_text().splitlines()]
require(all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match']for x in scan),'scan')
require(j(E/'NJF_FIXTURES.json')['count']==8,'fixtures')
require(len([r for r in records if r['kind']=='auditbatch'])==2,'audit count')

# Mutations are IN MEMORY; no predecessor evidence or validation input is edited.
rejected=[]
def reject(name,f):
 try:f()
 except ValueError:rejected.append(name);return
 raise ValueError('mutation accepted: '+name)
x=copy.deepcopy(R['NJF_K012']);x['limits']['memory.max']='17179869184';reject('cap increase',lambda:scope(x))
x=copy.deepcopy(R['NJF_K012']);x['swaps']='1';reject('swap',lambda:scope(x))
x=copy.deepcopy(R['NJF_K012']);x['env']['CARGO_TARGET_DIR']='/shared/target';reject('shared target',lambda:scope(x))
x=copy.deepcopy(R['NJF_K043']);reject('timeout is not control failure',lambda:negative(x,'CBMC timed out. Failed Checks: !same','!same'))
reject('pointer-only is not copied word failure',lambda:negative(R['NJF_K038'],'Failed Checks: l.alpha == alpha','l.ap0[power]'))
require(not list(E.rglob('__pycache__')),'bytecode')
require(not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024],'oversized file')
if (E/'NJF_CLOSED.json').exists():
 closed=j(E/'NJF_CLOSED.json');require({r for f in closed['functions']for r in f['rows']}=={'TX2:129','TX2:115'},'candidate scope')
 require(closed['credit_pending_next_ledger_gate'] and closed['authoritative_ledger_promotions']==0,'premature credit')
 require(all('AspisR1.NJF_Root.finish'in f['lean_roots']for f in closed['functions']),'deployed root inventory')
if (E/'NJF_RETENTION.json').exists():
 retained=j(E/'NJF_RETENTION.json');require(retained['modules']==len(scan) and retained['seed_hashes_rechecked'] and not retained['caches_deleted'],'retention')
 for info in retained['pin_chunks']:
  local=E/Path(info['path']).relative_to(B);require(sha(local.read_bytes())==info['sha256'],'retention chunk')
 require(len(j(E/'NJF_EXPORT.json')['files'])==18,'semantic export')
result=dict(status='PASS',kani_used=sum(r['kind']=='kani'for r in records),lean_link_audit_used=len(records)-sum(r['kind']=='kani'for r in records),extraction_used=0,pairs=[dict(window=w,positive=f'NJF_K{p:03}',negative=f'NJF_K{n:03}')for w,p,n,_ in pairs],semantic_modules=lean,raw_roots=len(raw),scan_modules=len(scan),rejected_mutations=rejected,credit_pending_next_ledger_gate=True)
(Path('/Users/dominic/ZK/.worktrees/cx-ledger14/evidence/ledger14-20261108/NJK_NJF_REVALIDATION.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['status','kani_used','lean_link_audit_used','raw_roots','scan_modules']}))
