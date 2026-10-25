#!/usr/bin/env python3
"""New output/coverage audit only; no compiler and no original full-payload rehash."""
import collections, hashlib, json, resource, sqlite3, subprocess, sys, time
from pathlib import Path
from Port29SDKDATA_diagnostic import E,T,OLD,CURRENT,SYS,pin,write
start=time.monotonic();receipt=json.loads((E/'Port29SDKDATA_diagnostic-2-receipt.json').read_text());assert receipt['accepted']
out=Path(receipt['env']['PORT29_DATA'])
db=sqlite3.connect('file:'+str(out/'Port29SDKDATA_complete-index.sqlite')+'?mode=ro',uri=True);db.execute('PRAGMA cache_size=-16000')
# All quantities are observations; accepted Port18 equality is explicitly alpha insensitive.
comparisons=[];transports=[];headers=[];kinds=collections.Counter();nconstants=0
with (out/'Port29SDKDATA_raw.jsonl').open() as f:
 for line in f:
  r=json.loads(line)
  if r['tag']=='part':headers.append(r);assert r['consistent']
  elif r['tag']=='constant':nconstants+=1;kinds[(r['side'],r['constant']['kind'])]+=1
  elif r['tag']=='transport':transports.append(r)
  else:comparisons.append(r)
assert nconstants==db.execute('SELECT count(*) FROM decl').fetchone()[0]==564052
expected={}
for tsv in ['Port29SDKDATA_compare.tsv','Port29SDKDATA_extra-compare.tsv']:
 for line in (out/tsv).read_text().splitlines():
  tag,p,q,*names=line.split('\t')
  for n in names:expected[(tag,p,q,n)]=True
observed={(r['tag'],r['left'],r['right'],r['name']) for r in comparisons}
assert observed==set(expected) and len(observed)==len(comparisons)
assert not any(r.get('missing_left') or r.get('missing_right') for r in comparisons)
root=[r for r in comparisons if r['tag']=='root-duplicate'];cross=[r for r in comparisons if r['tag']=='original-current'];extra=[r for r in comparisons if r['tag']=='full-original-current']
assert len({r['name'] for r in root})==328 and len({r['name'] for r in cross})==1059
limitation=dict(source=pin(SYS/'src/lean/Lean/Expr.lean'),
 exact_api='BEq Expr := Expr.eqv; binder names and annotations ignored. Expr.equal explicitly compares both.',
 consequence='Accepted Port18 sameDeclaration has all ConstantInfo fields but uses alpha equality for Expr fields. TRUE is NOT full binder-sensitive structural equality. FALSE is still a concrete declaration conflict under this comparison.',
 corrected_labels='same_constant_val and proof_only_same_full_type in raw diagnostic are alpha type comparisons, not binder-sensitive comparisons.',
 remaining='Before any claimed strict selection: Expr.equal on types, values/opaque proofs and recursor RHS, plus accepted full metadata checks; no third invocation authorized here.')
def status(r):
 return 'accepted_helper_equal_binder_check_pending' if r['sameDeclaration'] else 'same_alpha_type_theorem_proof_change' if r['proof_only_same_full_type'] else 'declaration_conflict'
def summarize(rows):
 grouped=collections.defaultdict(list)
 for r in rows:grouped[r['name']].append(r)
 return dict(observations=len(rows),names=len(grouped),observation_status=dict(collections.Counter(status(r) for r in rows)),
  name_status=dict(collections.Counter('declaration_conflict' if any(status(r)=='declaration_conflict' for r in rs) else
    'same_alpha_type_theorem_proof_change' if any(status(r)=='same_alpha_type_theorem_proof_change' for r in rs) else
    'accepted_helper_equal_binder_check_pending' for rs in grouped.values())))
for r in comparisons:r['qualified_status']=status(r)
write(out/'Port29SDKDATA_comparison-results.json',dict(limitation=limitation,comparisons=comparisons))
# Audit source-part/name requests and all genuinely new transport bytes.
requested={}
for line in (out/'Port29SDKDATA_export.tsv').read_text().splitlines():
 side,origin,m,p,dest,*names=line.split('\t');requested[(side,origin,m,p)]=set(names)
seen=collections.defaultdict(set);newedges=[];newpins=[];new_safety=[]
for r in transports:
 k=(r['side'],r['origin'],r['module'],r['source']);seen[k].update(r['names']);assert set(r['names'])<=requested[k]
 newpins.append(dict(**pin(r['path']),side=r['side'],origin=r['origin'],module=r['module'],source=r['source'],part=r['part'],names=r['names'],
  readback='Same invocation raw header/count/name and accepted sameDeclaration checks PASS; binder-sensitive Expr.equal NOT run'))
 expectednames={n for n, in db.execute('SELECT name FROM decl WHERE side=? AND origin=? AND module=? AND path=? AND part=?',(*k,r['part'])) if n in requested[k]}
 assert set(r['names'])==expectednames
 for n in r['names']:
  rows=list(db.execute('SELECT info FROM decl WHERE name=? AND side=? AND origin=? AND module=? AND path=? AND part=?',(n,*k,r['part'])))
  assert len(rows)==1
  c=json.loads(rows[0][0]);newedges.append(dict(side=r['side'],origin=r['origin'],module=r['module'],name=n,part=r['part'],transport=r['path'],**{key:c[key] for key in ['kind','unsafe','partial','dependencies']}))
  if c['unsafe'] or c['partial'] or c['kind']=='axiom':new_safety.append(dict(name=n,side=r['side'],module=r['module'],part=r['part'],kind=c['kind'],unsafe=c['unsafe'],partial=c['partial'],
   assessment='Raw view only. Earlier core public/server projections can be axiom placeholders for a later full body. No axiom/unsafe/partial exception or logical approval.'))
assert dict(seen)==requested
write(out/'Port29SDKDATA_incremental-transports.json',dict(transports=newpins,safety=new_safety,comparison_limit=limitation))
audit=json.loads((E/'Port29SDKDATA_audit.json').read_text());gp=next(p for p in audit['retained_outputs'] if p['path'].endswith('cross-origin-edges.jsonl'))
graph=collections.defaultdict(set);og=collections.defaultdict(set);known=set();oknown=set();factor=set();cs=set()
with Path(gp['path']).open() as f,(out/'Port29SDKDATA_final-cross-origin-edges.jsonl').open('x') as g:
 for line in f:
  r=json.loads(line);g.write(line);n=r['name'];graph[n].update(r['dependencies']);known.add(n)
  if r['side']=='ORIGINAL':og[n].update(r['dependencies']);oknown.add(n)
  else:
   cs.add(n)
   if r['module']=='S6SdkDependencyFactorV1':factor.add(n)
 for r in newedges:
  g.write(json.dumps(r,separators=(',',':'))+'\n');n=r['name'];known.add(n);graph[n].update(r['dependencies'])
  if r['side'] in ['ORIGINAL','CORE']:oknown.add(n);og[n].update(r['dependencies'])
def closure(seeds,g):
 seen=set();todo=list(seeds)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(g.get(n,set())-seen)
 return seen
wp=next(p for p in audit['retained_outputs'] if p['path'].endswith('union-worklist.json'));w=json.loads(Path(wp['path']).read_text())
aux='AspisR1.S2W_D189Wrappers.reserve._unsafe_rec';seeds=set(w['seeds'])-{aux}
rootseeds={l.split('\t')[1] for l in (OLD/'seeds.tsv').read_text().splitlines()}
reach=closure(seeds,graph);oreach=closure(rootseeds,og);rawreach=closure(w['seeds'],graph)
# Immutable Port18 provenance only: no live/closed object data opened.
canonical=json.loads(subprocess.check_output(['git','show','904745b496:evidence/port18coherence-20261024/canonical-manifest.json']))
p18={r['name']:r['origin'] for r in canonical['declarations']}
missing=json.loads((out/'Port29SDKDATA_new-provenance-323.json').read_text())
for r in missing:r['port18_manifest_origin']=p18.get(r['name'])
write(E/'Port29SDKDATA_complete-provenance-323.json',missing)
def available(n):
 return [dict(side=s,origin=o,module=m,path=p,part=i,kind=json.loads(c)['kind']) for s,o,m,p,i,c in db.execute('SELECT side,origin,module,path,part,info FROM decl WHERE name=?',(n,))]
gaps=[]
for n in sorted(reach-known):gaps.append(dict(name=n,complete_retained_parts=available(n),port18_manifest_origin=p18.get(n),
 current_available=n in cs,status='MISSING BODY; not a standard-leaf assumption or original equality'))
old77=set(w['raw_missing']);closed77=sorted(old77-(reach-known))
# Public main/server views can contain abstracted bodies: explicitly keep every view.
core_views=[]
for n in closed77:core_views.append(dict(name=n,origins=available(n)))
write(E/'Port29SDKDATA_final-gaps.json',dict(combined_raw_gaps=gaps,closed_prior77=core_views,original_seed_gaps=sorted(oreach-oknown),
 prior323_without_original_counterparts=[r['name'] for r in missing],
 selection='No first-wins selection. Highest complete private view is a source-aware candidate; earlier abstract/axiom projections remain raw evidence and require explicit comparison/rejection.'))
rootmissing=sorted(rootseeds-cs)
factor_missing={n:available(n) for n in sorted(factor-set(r['name'] for r in cross))}
interesting=[r for r in comparisons if r['name'] in ['AspisR1.S2W_D189Wrappers.first','AspisR1.S2W_EntryPrivileges.guards','AspisR1.S2W_EntryPrivileges.readonly','AspisR1.S2W_EntryPrivileges.writable','AspisR1.S2W_EntryPrivileges.accepted_privileges']]
write(E/'Port29SDKDATA_overlay-comparisons.json',dict(limitation=limitation,observations=interesting,factor_previously_unselected_counterparts=factor_missing))
# Index and transport files >5MB stay external. Pin genuinely NEW output bytes only.
output_names=['Port29SDKDATA_raw.jsonl','Port29SDKDATA_complete-index.sqlite','Port29SDKDATA_comparison-results.json',
 'Port29SDKDATA_incremental-transports.json','Port29SDKDATA_final-cross-origin-edges.jsonl',
 'Port29SDKDATA_new-closure.json','Port29SDKDATA_index-summary.json']
newoutputs=[pin(out/n) for n in output_names]
summary=dict(schema='Port29SDKDATA-complete-parts-qualified-comparisons-v1',status='RAW DATA INVENTORY/EXTRACTION PASS; strict binder-sensitive selection INCOMPLETE',
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=[sys.executable,'-B',str(Path(__file__).resolve())],
 tool=pin(__file__),receipt=pin(E/'Port29SDKDATA_diagnostic-2-receipt.json'),
 complete_part_inventory=dict(modules=4055,parts=len(headers),constants=nconstants,
  core_main=2433,core_server=2431,core_private=2431,original_main=1622,
  all_headers_consistent=True,values='Full ConstantInfo objects traversed in diagnostic, retained raw in input; subset serialized without modification'),
 root_duplicates=summarize(root),original_current=summarize(cross),full_original_factor=summarize(extra),comparison_limit=limitation,
 original323=dict(no_original_or_core_counterpart=323,current_only=265,port18_manifest_only=17,absent_both_selected=41),
 factor=dict(current_names=169,original_full_counterparts=len({r['name'] for r in extra}),
  missing_original=[n for n,v in factor_missing.items() if not v],newly_found_original=[n for n,v in factor_missing.items() if v]),
 root_seeds=dict(total=67,in_current=67-len(rootmissing),missing_current=rootmissing),
 incremental=dict(modules=len(requested),raw_transports=len(transports),bytes=sum(p['bytes'] for p in newpins),
  name_origin_requests=sum(map(len,requested.values())),constant_observations=len(newedges),unique_names=len({r['name'] for r in newedges}),
  raw_readback_pass=True,binder_sensitive_readback=False,unsafe_partial_axiom_observations=len(new_safety)),
 combined=dict(logical_seed_candidates=len(seeds),reachable=len(reach),raw_missing=len(reach-known),closed_prior77=closed77,
  raw_seed_count=len(w['seeds']),raw_reachable=len(rawreach),auxiliary_reachable=aux in reach,fixed_point=True,
  original_67_reachable=len(oreach),original_67_missing=len(oreach-oknown),safe_logical_closure=False,kernel_ready=False),
 external_outputs=newoutputs,external_transport_manifest=next(p for p in newoutputs if p['path'].endswith('incremental-transports.json')),
 validation_reused='Prior source/payload/2.8GB byte/hash/8-round graph audits; historical source and proof receipts unchanged. Fresh stat continuity, runtime/API/source hashes and new-output hashes separately recorded.',
 new_print_axioms='N/A: raw IO/noncompiler data audits',lean_used_here=2,global_actual=351,global_ceiling=368,
 budget_remaining=dict(total=17,here=0,unassigned=5,reserved_kernel_consumer=5,carry=7),
 security_targets='BOTH NOT YET ESTABLISHED',exit_status=0,wall_seconds=time.monotonic()-start,
 peak_rss_bytes=resource.getrusage(0).ru_maxrss,swaps=resource.getrusage(0).ru_nswap)
assert summary['peak_rss_bytes']<512*1024**2
write(E/'Port29SDKDATA_final-audit.json',summary)
print(json.dumps({k:summary[k] for k in ['root_duplicates','original_current','full_original_factor','factor','incremental','combined','wall_seconds','peak_rss_bytes']}))
