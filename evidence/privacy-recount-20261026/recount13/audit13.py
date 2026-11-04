"""Recount13: immutable source, trace and receipt inspection; launches no proof tools."""
import json, subprocess, hashlib, lzma, re, collections, datetime
from pathlib import Path
P=Path(__file__).resolve().parent; B=P.parent
BASE='33b7941bbab2c10cdd7f28dd8c0c0792577f2242'
def git(*a): return subprocess.check_output(['git',*a])
def dump(n,x): (P/n).write_text(json.dumps(x,indent=1)+'\n')
if not (P/'pins.json').exists():
 refs={'research':BASE,'rw':'refs/remotes/origin/codex/cx-prover-rw-20261023',**{k:'codex/pv-'+k+'-'+d for k,d in [('b3p6','20261028'),('evhB','20261103'),('stx','20261104'),('stxb','20261104'),('own2','20261104'),('evh','20261029'),('runjoin','20261026'),('uc','20261029'),('evhc','20261029')]}}
 remote=git('ls-remote','origin','refs/heads/codex/cx-prover-rw-20261023').decode().strip()
 pins={'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'worktree':str(Path.cwd()),'branch':'codex/pv-recount13-20261104','base':BASE,'refs':refs,'revisions':{k:git('rev-parse',v).decode().strip() for k,v in refs.items()},'shared_origin_query':remote,'local_candidate_excluded':git('rev-parse','refs/heads/codex/cx-prover-rw-20261023').decode().strip(),'candidate_resolution':'Shared origin head verified read-only by git ls-remote; stale local branch excluded. No fetch or push.'}
 assert remote.split()[0]==pins['revisions']['rw']; dump('pins.json',pins)
pins=json.loads((P/'pins.json').read_text()); revs=dict(pins['revisions']); manifest={}; cache={}; trees={}
def tree(k):
 if k not in trees: trees[k]=set(git('ls-tree','-r','--name-only',revs[k]).decode().splitlines())
 return trees[k]
def read(k,path):
 if Path(path).is_absolute():path=str(Path(path).relative_to(Path.cwd()))
 if (k,path) in cache:return cache[k,path]
 if path not in tree(k):return None
 blob=git('rev-parse',revs[k]+':'+path).decode().strip(); b=git('show',revs[k]+':'+path)
 manifest[k+':'+path]={'ref':k,'revision':revs[k],'path':path,'blob':blob,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'storage':'committed Git blob'}
 cache[k,path]=b;return b
def txt(k,p):
 b=read(k,p);return None if b is None else b.decode()
def obj(k,p):return json.loads(read(k,p))
resolved={}
def module(k,m):
 if (k,m) in resolved:return resolved[k,m]
 known=[]
 if m.startswith('R1Z.ProverRwFull'):known.append('docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean')
 if m.startswith('PV_B3P_'):known.append('evidence/pv-b3p6-20261028/lean/'+m+'.lean')
 known+=['lean/'+m.replace('.','/')+'.lean','docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean']
 for p in known:
  if p in tree(k):resolved[k,m]=(txt(k,p),p);return resolved[k,m]
 opts=[s for s in tree(k) if s.endswith('/'+m.replace('.','/')+'.lean') or s==m.replace('.','/')+'.lean']
 if not opts:opts=[s for s in tree(k) if s.endswith('/'+m.split('.')[-1]+'.lean')]
 if len(opts)!=1:return None,None
 p=opts[0];resolved[k,m]=(txt(k,p),p);return resolved[k,m]
# Each historical defining path at every current pin, including own2. No moving reads.
prior=obj('research',str(B/'recount12/rows12.json'))
old_audit=obj('research',str(B/'recount12/definition-audit12.json'))
defs=[]
for a in old_audit:
 sources=[]; changes=[]
 for k in pins['revisions']:
  for path in sorted({s['path'] for s in a['sources']}):
   b=read(k,path)
   if b is None:continue
   rec=dict(manifest[k+':'+path]); olds=[s for s in a['sources'] if s['ref']==k and s['path']==path]
   if not olds:olds=[s for s in a['sources'] if s['ref']=='research' and s['path']==path]
   rec['prior_identical']=any(s['sha256']==rec['sha256'] for s in olds);sources.append(rec)
   if not rec['prior_identical']:changes.append({'ref':k,'path':path,'sha256':rec['sha256']})
 defs.append({'id':a['id'],'sources':sources,'changed':changes})
dump('definition-audit13.json',defs)
# Retained CBMC streams: inspect real properties separately from reachability probes.
K='evidence/k3-audit-20261030/k4trace/'
status=obj('research',K+'k4trace-status.json')
payload=json.loads(lzma.decompress(read('research',K+'source-payload.json.xz')))
retained=json.loads(lzma.decompress(read('research',K+'retained-k3-sources.json.xz')))
checks=[]
for supplied in status['credits']:
 c=supplied['credit']; out={'credit':c,'decision':'RESTORE','qualified_scope':supplied.get('scope','Original bounded PathBuf <=4 byte P6 source/model scope only; native std transfer withheld.'),'source_sha256':supplied['source_sha256'],'reason':supplied['reason'],'scopes':[],'raw_results':[]}
 candidates=list(payload.values())+[s for v in retained.values() for s in v.values()]
 sources=[s for s in candidates if hashlib.sha256(s.encode()).hexdigest()==supplied['source_sha256']]
 assert sources,c
 out['primary_source_rehashed']=True
 out['primary_source_assertions']=[{'line':i+1,'text':v} for i,v in enumerate(sources[0].splitlines()) if 'assert' in v or 'dst.add' in v or 'byte_index=' in v]
 for run in dict.fromkeys([supplied['positive'],supplied['control']]):
  r=obj('research',K+f'host/{run}/receipt.json'); ident=obj('research',K+f'host/{run}/identity.json')
  assert all(x['match'] and x['expected']==x['actual'] for x in ident['sources']); assert all(x['match'] for x in ident['tools'].values())
  assert r['swap']==0 and r['limits']['memory.swap.max']=='0'
  assert r['limits']['memory.max']=='8589934592'
  ad=obj('research',K+f'host/{run}/admission.json'); barrier=obj('research',K+f'host/{run}/barrier.json')
  assert ad['allowed'] and barrier['allowed']
  output=txt('research',K+f'host/{run}/output.log')
  out['scopes'].append({'run':run,'receipt':r,'admission_allowed':True,'barrier_allowed':True,'output_verdict_lines':[s for s in output.splitlines() if 'SUCCESSFUL' in s or 'FAILED' in s or 'Complete -' in s]})
  for path in sorted(tree('research')):
   if not path.startswith(K+f'host/{run}/cbmc-') or not (path.endswith('.json') or path.endswith('.json.xz')) or path.endswith('-command.json'):continue
   raw=read('research',path); raw=lzma.decompress(raw) if path.endswith('.xz') else raw
   results=[r for z in json.loads(raw) for r in z.get('result',[])]
   if not results:continue
   failed=[r for r in results if r['status']=='FAILURE' and r.get('sourceLocation',{}).get('propertyClass')!='reachability_check']
   parsed=[]
   for r0 in failed:
    trace=r0.get('trace',[]); assert trace and trace[-1]['stepType']=='failure'
    # Inspect actual native caller assignments/calls, not provider trace excerpts.
    events=[]
    for i,e in enumerate(trace):
     loc=e.get('sourceLocation',{}); f=loc.get('file','')
     if f in ['lib.rs','src/sealed.rs','src/indexed.rs'] or (e.get('stepType')=='function-call' and 'assert_failed' in str(e)):
      events.append({'step':i,'kind':e['stepType'],'lhs':e.get('lhs'),'value':e.get('value'),'location':loc,'function':e.get('function')})
    parsed.append({'property':r0['property'],'description':r0['description'],'location':r0.get('sourceLocation'),'trace_steps':len(trace),'caller_events':events,'terminal':trace[-1]})
   out['raw_results'].append({'path':path,'uncompressed_sha256':hashlib.sha256(raw).hexdigest(),'properties':len(results),'probe_failures':sum(r['status']=='FAILURE' and r.get('sourceLocation',{}).get('propertyClass')=='reachability_check' for r in results),'non_probe_failures':parsed})
  # Full symbol maps are immutable inputs too, mapped to each goto by symbols-index.
  symbols=obj('research',K+f'host/{run}/symbols-index.json')
  out['scopes'][-1]['symbols_index']=symbols
  for p in tree('research'):
   if p.startswith(K+f'host/{run}/') and (p.endswith('type_map.json.xz') or p.endswith('pretty_name_map.json.xz')):read('research',p)
 failures=[v for x in out['raw_results'] for v in x['non_probe_failures']]
 assert len(failures)==(2 if c.startswith('K') else 1),(c,len(failures))
 if c=='C044':assert failures[0]['location']['line']=='74' and 'len != r.len()' in failures[0]['description']
 if c=='C084':assert failures[0]['location']['line']=='145'
 if c in ['C088','C089']:
  line='105' if c=='C088' else '123'; assert any(e['location'].get('line')==line and e['location'].get('file')=='src/sealed.rs' for e in failures[0]['caller_events'])
 if c.startswith('K'):assert {r['location']['line'] for r in failures}=={'42','44'}
 assert any(not x['non_probe_failures'] for x in out['raw_results']),c
 checks.append(out)
dump('k4-restore-check.json',{'method':'Independently parsed complete raw CBMC result/trace streams, rehashed archived complete primary source; verified identities, admissions, receipts and symbol indices. Reachability probes are driver instrumentation, separately recorded. No Kani executed.','checks':checks,'historical_credit_counts_after_restore':{'RESTORED':26,'UNAFFECTED':81,'SUSPENDED':195,'WITHDRAWN':3},'new_K93109_K93111':'restored projection only; excluded from 305 historical count','C002':'SUSPENDED','Lean':0,'Kani':0})
# Rederive exact same consumer-root membership (source graphs only).
rows=[]
for old in prior:
 r={k:v for k,v in old.items() if not re.search(r'(?:11|12)$',k) and k!='historical_row'}
 r.update(historical_row='../recount12/rows12.json#'+r['id'],recount12_status=old['recount12_status'],recount13_status=old['recount12_status'],recount13_class=old['recount12_class'],recount13_basis='Recount12 scoped statement, qualifications and residual retained after defining-source comparison; see historical_row.',definition_witnesses13='definition-audit13.json#'+r['id'],import_witnesses13='import-membership13.json#'+r['id'])
 rows.append(r)
by={r['id']:r for r in rows}
for id in ['V177','V180']:
 r=by[id]; old=next(x for x in prior if x['id']==id)
 assert old['k4_excluded_support']==['C044'] and old['closure_route']=='P6 gate'
 r.update(recount13_status='CLOSED-ON-CANDIDATE',dependency_bucket=None,k4_current_kani_support=['C044'],k4_excluded_support=[],recount13_basis='RESTORE exactly pre-Recount12 C044-supported bounded PathBuf source/model P6 scope: length <=4, arbitrary full-width checked get query. Intended equal-zero-length control at lib.rs:74 verified in full trace; positive passes at e2e80df1 source. Native/std transfer remains withheld; no whole deployed or privacy closure. No stronger domain or Result law credited.')
by['V179']['recount13_basis']='Structural complete-body String-to-Path closure unchanged; C084 restored only as historical two-byte bounded stubbed credit, not its current support.'
by['V233']['recount13_basis']='Independent typed structural consumed_instance closure and complete Result scope unchanged. C088/C089 restored only at original bounded stubbed coordinate scopes; neither replaces C002 (SUSPENDED) nor discharges the typed association.'
for id in ['V241','V244','V245']:
 by[id]['recount13_basis']='OPEN b. D650 27/217 local conditional caller certificates (73 sites), not whole original-entry composition, original-ops equation, opaque associations or DeployedWrapper557. NativePending/NativeFault/NativeEffects/ResourceTimingIndependence and concrete OWNER installation retained. K93303 timeout and K93309 unconfirmed earn no credit; C156 stays suspended.'
for id in ['V263','V400','V403']:
 by[id]['recount13_basis']='OPEN b. D646-D649 original activation/place obstruction remains. D653 typed-memory interface supplies proved conditional observations at supplied places, not native places. FreshAllocationValidity is a NEW NAMED PREMISE below the endpoint under rdea-1/V370, not proved, not T. Four D625 thread contracts remain OPEN. D651/D656 instrumented translator route/patch pending; no patched extraction credit.'
by['V370']['recount13_basis']='OPEN b. Retain compiler preservation obligation; D653 adds one named below-endpoint FreshAllocationValidity resources granted reached_state world-answer premise under rdea-1/V370. Does not discharge allocator correctness, native layout or source-place association; no T field or endpoint premise added.'
oldpins=obj('research',str(B/'recount12/pins.json'))['revisions']; hist={'join':'c3b99bc9d96b674a0c9d24c7cabdbc2711e5f1a2'}; revs.update(hist)
roots=[(x['ref'],x['root']) for x in obj('research',str(B/'recount12/import-closures12.json')) if not x.get('new_endpoint')]
closures=[]
for k,root in roots+[('rw','PV_MEAS_Deployed')]:
 paths={root:[root]};queue=[root];missing=[]
 for m in queue:
  if not m.startswith(('R1Z.','R0Z.','PV_')):continue
  s,p=module(k,m)
  if s is None:missing.append(m);continue
  for d in re.findall(r'^import\s+(\S+)',s,re.M):
   if d not in paths:paths[d]=paths[m]+[d];queue.append(d)
 closures.append({'ref':k,'revision':revs[k],'root':root,'new_endpoint':root=='PV_MEAS_Deployed','paths':paths,'unresolved_project_modules':missing})
members=[]
for r in rows:
 th=r.get('closure_theorem') if r['recount13_status']=='CLOSED-ON-CANDIDATE' else None
 if th:
  old=next(x for x in prior if x['id']==r['id']);m=old.get('closing_statement12',old.get('closing_statement11',{})).get('module')
  m=m or r.get('closure_source_module13') or ('.'.join(th.split('.')[:2]) if th.startswith('R1Z.') else th.split('.')[0])
 else:
  d=r.get('definition','').split('#')[0];m=('R1Z.'+Path(d).stem if '/lean/prover-rw-' in d else d.split('/lean/')[-1][:-5].replace('/','.')) if '/lean/' in d and d.endswith('.lean') else None
 ws=[];new=[]
 if m:
  source,p=module('rw',m)
  if th:
   assert source is not None,(r['id'],m)
   r['closing_statement13']={'ref':'rw','revision':revs['rw'],'module':m,'path':p,'sha256':hashlib.sha256(source.encode()).hexdigest(),'theorem':th}
  for cl in closures:
   if m not in cl['paths']:continue
   s,_=module(cl['ref'],m);norm=lambda t:re.sub(r'^import[^\n]*\n','',t,flags=re.M)
   if not th or (s and source and norm(s)==norm(source)):
    w={'ref':cl['ref'],'root':cl['root'],'path':cl['paths'][m],'scope':'import membership, not discharge'};(new if cl['new_endpoint'] else ws).append(w)
 members.append({'id':r['id'],'module':m,'witnesses':ws,'event_endpoint_witnesses':new})
 r['in_headline_closure13']='research' if any(w['ref']=='research' for w in ws) else 'candidate' if ws else 'neither'
 if r['recount13_status']!='OPEN':r['dependency_bucket']=None
 else:assert r['dependency_bucket'] in 'abcd'
dump('rows13.json',rows);dump('import-membership13.json',members);dump('import-closures13.json',closures)
dump('totals.json',{'rows':len(rows),'classes':dict(collections.Counter(r['recount13_class'] for r in rows)),'statuses':dict(collections.Counter(r['recount13_status'] for r in rows)),'open_dependencies':dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount13_status']=='OPEN')),'all_row_imports':dict(collections.Counter(r['in_headline_closure13'] for r in rows)),'status_changes':[{'id':r['id'],'before':r['recount12_status'],'after':r['recount13_status'],'reason':r['recount13_basis']} for r in rows if r['recount12_status']!=r['recount13_status']],'credits_after_restore':{'RESTORED':26,'UNAFFECTED':81,'SUSPENDED':195,'WITHDRAWN':3},'endpoint_premises_removed_added_weakened':[0,0,0],'new_named_premises_below_endpoint':['PV_OWN2_FreshAllocation.FreshAllocationValidity resources granted reached_state'],'Lean':0,'Lean_budget':40,'Kani':0,'Kani_budget':0,'Env_J':'93800-93839 unused','target':'Target not yet established'})
dump('manifest.json',list(manifest.values()))
print('PASS source/trace/row inspection',len(rows),'rows;',len(manifest),'Git inputs; defining changes',collections.Counter(x['path'] for a in defs for x in a['changed']))
