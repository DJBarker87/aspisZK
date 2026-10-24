#!/usr/bin/env python3
"""Independent data audit of the single Strict-v3 invocation; no Lean launch."""
import collections,hashlib,itertools,json,resource,sqlite3,subprocess,time
from pathlib import Path
from Port29SDKDATA_diagnostic import E,T,OLD,CURRENT,pin,write
from Port29SDKDATA_strict3 import PREP,REC,NEW,obj
start=time.monotonic();r=json.loads(REC.read_text());assert r['accepted'] and r['job_cumulative_charged']==3
prep=json.loads(PREP.read_text());out=Path(prep['directory'])
comparisons=[];parts=[];records=[];transports=[];counter=[]
with (out/'Port29SDKDATA_raw.jsonl').open() as f:
 for line in f:
  x=json.loads(line)
  if x['tag']=='api-counterexample':counter.append(x)
  elif x['tag']=='part':parts.append(x);assert x['consistent']
  elif x['tag']=='constant':records.append(x)
  elif x['tag']=='transport':transports.append(x)
  else:comparisons.append(x)
expected=set()
for line in (out/'Port29SDKDATA_compare.tsv').read_text().splitlines():
 tag,p,q,*names=line.split('\t')
 expected.update((tag,p,q,n) for n in names)
assert {(x['tag'],x['left'],x['right'],x['name']) for x in comparisons}==expected
assert len(comparisons)==len(expected)==7758
assert not any(x.get('missing_left') or x.get('missing_right') for x in comparisons)
assert len(counter)==4 and all(not x['strict_v3'] and x['reflexive'] for x in counter)
# The syntax-source-info counterexample is a real limitation of Expr.equal alone.
assert next(x for x in counter if x['name']=='metadata-syntax-source-info')['expr_equal']
groups=collections.defaultdict(list)
for x in comparisons:groups[x['tag']].append(x)
def status(xs):
 if all(x['strict_v3'] for x in xs):return 'strict_equal'
 if all(x['sameDeclaration'] for x in xs):return 'alpha_equal_strict_different'
 if all(x['strict_type'] and (x['sameDeclaration'] or x['proof_only_same_full_type']) for x in xs):return 'strict_type_theorem_proof_variant'
 return 'declaration_conflict'
def summary(rows):
 g=collections.defaultdict(list)
 for x in rows:g[x['name']].append(x)
 return dict(observations=len(rows),names=len(g),name_status=dict(collections.Counter(status(xs) for xs in g.values())),
  observation_strict_equal=sum(x['strict_v3'] for x in rows),
  type_different_names=sorted(n for n,xs in g.items() if any(not x['strict_type'] for x in xs)),
  value_different_names=sorted(n for n,xs in g.items() if any(not x['strict_value'] for x in xs)))
assert summary(groups['root-duplicate'])['names']==328
assert summary(groups['original-current'])['names']==1059
assert len(groups['full-original-current'])==169
assert all(x['strict_v3'] for x in comparisons if x['tag'].startswith('source-readback:'))
requests={}
for line in (out/'Port29SDKDATA_export.tsv').read_text().splitlines():
 side,origin,m,p,dest,*names=line.split('\t');requests[(side,origin,m,p)]=set(names)
newdb=sqlite3.connect('file:'+str(out/'Port29SDKDATA_focused.sqlite')+'?mode=ro',uri=True)
old=sqlite3.connect('file:'+prep['prior_sqlite']['path']+'?mode=ro',uri=True)
for db in [newdb,old]:db.execute('PRAGMA cache_size=-16000');db.execute('PRAGMA mmap_size=0')
def info(side,origin,m,p,part,n):
 found=[]
 for db in [newdb,old]:
  found.extend(db.execute('SELECT info FROM decl WHERE side=? AND origin=? AND module=? AND path=? AND part=? AND name=?',(side,origin,m,p,part,n)))
 assert len(found)==1,(side,origin,m,p,part,n,len(found))
 return json.loads(found[0][0])
seen=collections.defaultdict(set);edges=[];transportpins=[]
for t in transports:
 key=(t['side'],t['origin'],t['module'],t['source']);assert set(t['names'])<=requests[key];seen[key].update(t['names'])
 transportpins.append(dict(**pin(t['path']),**{k:t[k] for k in ['side','origin','module','source','part','names']},strict_source_readback=True))
 for n in t['names']:
  c=info(*key,t['part'],n);edges.append(dict(side=t['side'],origin=t['origin'],module=t['module'],source=t['source'],part=t['part'],transport=t['path'],**c))
# Requested absent names are not silently manufactured. Every nonempty source request had output.
assert set(seen)==set(requests)
assert all(seen[k]<=requests[k] for k in seen)
newcurrent=[dict(side=x['side'],origin=x['origin'],module=x['module'],source=x['path'],part=x['part'],transport=x['path'],**x['constant']) for x in records if x['side']=='CURRENT-INCREMENTAL']
assert len(newcurrent)==1220 and len({x['name'] for x in newcurrent})==1219
currentparts=[x for x in parts if x['side']=='CURRENT-INCREMENTAL']
assert len(currentparts)==141 and all(x['imports']==[] and x['extra']==0 and x['entries']==0 for x in currentparts)
prior=json.loads((E/'Port29SDKDATA_final-audit.json').read_text());gp=next(x for x in prior['external_outputs'] if x['path'].endswith('final-cross-origin-edges.jsonl'))
graph=collections.defaultdict(set);known=set();og=collections.defaultdict(set);oknown=set();current_names=set();old_original_names=set();allcurrent=collections.defaultdict(set)
newpath=out/'Port29SDKDATA_Strict-v3-cross-origin-edges-final.jsonl'
with Path(gp['path']).open() as f,newpath.open('x') as g:
 for line in f:
  x=json.loads(line);g.write(line);n=x['name'];known.add(n);graph[n].update(x['dependencies'])
  if x['side'] in ['ORIGINAL','CORE']:oknown.add(n);og[n].update(x['dependencies']);old_original_names.add(n)
  if x['side']=='CURRENT':current_names.add(n);allcurrent[n].add(str(CURRENT/'transport'/(x['module'].replace('.','/')+'.olean')))
 for x in newcurrent+edges:
  g.write(json.dumps(x,separators=(',',':'))+'\n');n=x['name'];known.add(n);graph[n].update(x['dependencies'])
  if x['side'] in ['ORIGINAL','CORE']:oknown.add(n);og[n].update(x['dependencies']);old_original_names.add(n)
  if x['side']=='CURRENT-INCREMENTAL':current_names.add(n);allcurrent[n].add(x['source'])
def closure(seeds,g):
 seen=set();todo=list(seeds)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(g.get(n,set())-seen)
 return seen
wa=json.loads((E/'Port29SDKDATA_audit.json').read_text());wp=next(x for x in wa['retained_outputs'] if x['path'].endswith('union-worklist.json'));w=json.loads(Path(wp['path']).read_text());aux='AspisR1.S2W_D189Wrappers.reserve._unsafe_rec'
oldseeds=set(w['seeds'])-{aux};newseeds=set(json.loads((NEW/'input.json').read_text())['seeds'])-{aux};seeds=oldseeds|newseeds
rootseeds={l.split('\t')[1] for l in (OLD/'seeds.tsv').read_text().splitlines()}
reach=closure(seeds,graph);oreach=closure(rootseeds,og);oldreach=closure(oldseeds,graph);gaps=reach-known
# Preserve actual new origin inventories and explicit prerequisite per missing name.
can=obj('evidence/port18coherence-20261024/canonical-manifest.json');p18={x['name']:x['origin'] for x in can['declarations']}
old54=json.loads((E/'Port29SDKDATA_final-gaps.json').read_text())['combined_raw_gaps']
found54=[];origins=collections.defaultdict(list)
for x in newcurrent+edges:
 origins[x['name']].append({k:x.get(k) for k in ['side','origin','module','source','part','transport','kind','unsafe','partial']})
for row in old54:
 n=row['name'];found54.append(dict(name=n,previous_port18_origin=row['port18_manifest_origin'],actual_new_origins=origins[n],body_now_available=n in known,still_graph_gap=n in gaps,old_original_equal='NOT ESTABLISHED by current/raw availability'))
newmissing=[]
for n in sorted(gaps):
 providers=[]
 if n.startswith('S8OwnedP6.'):
  stem=n.removeprefix('S8OwnedP6.')
  type_declarations={'CodecError','CodecError.NonCanonical','aspis_core.field.M31',
   'aspis_core.field.CM31','aspis_core.field.CM31.a','aspis_core.field.CM31.b','aspis_core.field.CM31.mk',
   'aspis_core.field.QM31','aspis_core.field.QM31.c0','aspis_core.field.QM31.c1','aspis_core.field.QM31.mk'}
  providers=['S8OwnedP6.Types' if stem in type_declarations else 'S8OwnedP6.Funs']
 prereq='Release full matching original S8OwnedP6.Types/Funs objects as regular closed pinned files, including generated private helpers; current symlinks are unauthorized targets.'
 if n=='Bool.eq_true_of_not_eq_false':
  providers=['historical Bool helper (not present in retained complete Lean4.32 core)'];prereq='Release pinned historical helper body or explicitly replay unchanged OraclePortCompactDraft source parse_header against available Bool lemmas, compare strict public type and kernel audit. No theorem allocation here.'
 source_module=providers[0] if providers and providers[0].startswith('S8OwnedP6.') else None
 source_path=('docs/research/100bit-spend-path-20261013/lean/'+source_module.replace('.','/')+'.lean') if source_module else None
 # Generated field/constructor/matcher/proof suffixes are tied to containing
 # immutable declarations, not assumed to be recoverable from selected lists.
 source_pin=None
 if source_path:
  source_bytes=subprocess.check_output(['git','show','904745b496:'+source_path])
  source_pin=dict(revision='904745b496c1eb84871aacd83b8f9d42f0762613',path=source_path,bytes=len(source_bytes),sha256=hashlib.sha256(source_bytes).hexdigest())
 newmissing.append(dict(name=n,providing_module_candidates=providers,immutable_source=source_pin,prerequisite=prereq))
# Exact stale proof consumers: body source vs readback pins remain distinct.
backrefs=[]
with newpath.open() as f:
 for line in f:
  x=json.loads(line);ds=set(x['dependencies'])&({'Bool.eq_true_of_not_eq_false','List.filterMap_congr'}|gaps)
  if ds:backrefs.append(dict(name=x['name'],side=x['side'],module=x['module'],missing_dependencies=sorted(ds),source=x.get('source')))
# The baseline constants JSONL emitted first observations only. Its43 duplicates
# must be enumerated from the release's duplicate provenance, never inferred absent.
release_duplicates=[];paths=collections.defaultdict(list)
for m,p in json.loads((NEW/'audit-input.json').read_text())['transport']:paths[m].append(p)
new_presence={(x['module'],x['name'],x['source']) for x in newcurrent}
for line in (NEW/'duplicates-combined.jsonl').read_text().splitlines():
 d=json.loads(line);variants=[]
 for label in [d['first'],d['second']]:
  candidates=[]
  for p in paths[label]:
   if str(NEW) in p and (label,d['name'],p) not in new_presence:continue
   candidates.append(p)
  variants.append(dict(module=label,candidate_raw_paths=candidates))
 release_duplicates.append(dict(name=d['name'],variants=variants,owner_helper_equal=d['identical'],strict_status='NOT CHECKED HERE: complete duplicate provenance was absent from first-observation baseline graph; no fourth diagnostic'))
assert len(release_duplicates)==43
# Additional concrete pair worklists for new Port18 variants, ready for a separately authorized consumer.
variant_pairs=[]
for n,rs in origins.items():
 ps=sorted({x['transport'] for x in rs if x['transport']})
 if len(ps)>1:
  for a,b in itertools.combinations(ps,2):variant_pairs.append(dict(name=n,left=a,right=b,status='raw source-readback verified separately; cross-origin strict comparison pending'))
comp_packet=dict(counterexamples=counter,comparisons=comparisons,current_duplicate_provenance=release_duplicates,new_variant_pairs=variant_pairs)
write(out/'Port29SDKDATA_Strict-v3-comparisons-final.json',comp_packet)
write(out/'Port29SDKDATA_Strict-v3-transports-final.json',dict(transports=transportpins,readback='strictDeclaration source part, every serialized ConstantInfo, same diagnostic',selection='All variants retained; not a kernel-ready environment'))
write(E/'Port29SDKDATA_Strict-v3-final-gaps.json',dict(prior54=found54,remaining=newmissing,backreferences=backrefs,conflicting13=sorted({x['name'] for x in groups['original-current'] if not x['sameDeclaration'] and not x['proof_only_same_full_type']}),
 list_filterMap_current_only=dict(module='Mathlib.Data.List.Basic',raw_body_available=True,original_body_equality=False,unchanged_source_replay_candidates=['S2W_FirstOccurrence.first_occurrence','S2W_OuterOccurrences.second_occurrence'])))
# Recompute323 provenance from actual focused full index, not selected manifest alone.
old323=json.loads((E/'Port29SDKDATA_complete-provenance-323.json').read_text());provenance=[]
for row in old323:
 n=row['name'];p18rows=[]
 for s,o,m,p,i,c in newdb.execute('SELECT side,origin,module,path,part,info FROM decl WHERE name=?',(n,)):
  p18rows.append(dict(side=s,origin=o,module=m,path=p,part=i,kind=json.loads(c)['kind']))
 provenance.append(dict(name=n,retained_original_core_available=n in old_original_names,current_body_available=n in current_names,new_full_module_observations=p18rows,old_original_equal=False,selected_raw_export_origins=origins[n]))
write(out/'Port29SDKDATA_Strict-v3-provenance-323-final.json',provenance)
# Exact input/output integrity is separate from stat continuity.
assert all(pin(x['path'])==x for x in prep['inputs'])
newpins=[pin(p) for p in sorted(out.rglob('*')) if p.is_file() and p.name not in ['Port29SDKDATA_preparation-v1-not-launched.json','Port29SDKDATA_preparation-v2-not-launched.json']]
module_counts=collections.Counter(x['module'] for x in newcurrent)
availability={m:dict(observations=module_counts[m],raw_path=str(NEW/'transport'/(m+'.olean')),pin=next(p for p in prep['inputs'] if p['path']==str(NEW/'transport'/(m+'.olean')))) for m in ['S6SdkSourceCutTypesV1','S6SdkSourceCutReuseV1','S6SdkEnclosingCutsV1','S6SdkFirstObjectEquivalenceV1','S6SdkOriginalObjectCallerV1','S1SdkSourceCutNumericV1','S1SdkPreparedChallengeRangesV1']}
assert all(x['observations'] for x in availability.values())
summary=dict(schema='Port29SDKDATA-Strict-v3-data-audit',excluded_preliminary_audits='v1 had heuristic source-module mapping; v2 noncompiler attempt refused overwrite and failed. All preliminary/partial outputs retained and excluded as final conclusions; no further Lean invocation',status='Focused strict comparison/readback and released raw-body acquisition PASS; coherent kernel selection OPEN',
 diagnostic_receipt=pin(REC),source_revision_at_diagnostic=r['source_revision'],source=r['source'],audit_source=pin(__file__),
 exact_api=counter,root_duplicates=summary(groups['root-duplicate']),original_current=summary(groups['original-current']),factor=summary(groups['full-original-current']),
 previous194_readback=dict(transports=194,observations=sum(len(xs) for tag,xs in groups.items() if tag.startswith('source-readback:')),strict=True),
 focused_index=dict(modules=len(parts),constants=len(records),current_new_observations=len(newcurrent),current_new_unique_names=len({x['name'] for x in newcurrent}),
 closed_Port18_and_Port17_modules=10,all_actual_parts_consistent=True),
 new_transports=dict(files=len(transports),bytes=sum(x['bytes'] for x in transportpins),sources=len(requests),observations=len(edges),names=len({x['name'] for x in edges}),strict_source_readback=True),
 graph=dict(logical_seed_candidates=len(seeds),reachable=len(reach),missing=len(gaps),known_names=len(known),old190_seed_reachable=len(oldreach),old190_seed_missing=len(oldreach-known),
  original67_retained_original_core_only_reachable=len(oreach),original67_retained_original_core_only_missing=len(oreach-oknown),
  combined_original_incomplete=True,kernel_ready=False,auxiliary_reachable=aux in reach,fixed_point=True,
  union_rule='ALL actual serialized variant edges, including different Port18 and retained-original bodies; no first-wins selection'),
 prior54=dict(closed=sum(x['body_now_available'] for x in found54),remaining=sum(not x['body_now_available'] for x in found54),closed_names=sorted(x['name'] for x in found54 if x['body_now_available'])),
 release_modules=availability,stale_six_missing_statement='EXPLICITLY SUPERSEDED: all six previous modules plus S1 preparation/challenge-range raw data actually read',
 current_release_duplicates=dict(recorded=43,owner_alpha_equal_reused=True,strict_checked_here=0,strict_worklist_status='PENDING; no inference of strict equality or closed coherent environment'),
 further_variant_worklist=dict(pairs=len(variant_pairs),executed=0,status='Available raw candidates only; separately authorized strict/kernel consumer prerequisite'),
 original323=dict(no_retained_original_core_counterpart=sum(not x['retained_original_core_available'] for x in provenance),
  current_body_available=sum(x['current_body_available'] for x in provenance),port18_or_incremental_full_observation=sum(bool(x['new_full_module_observations']) for x in provenance),old_original_equality_established=0),
 proof_refreshes=dict(EntryPrivileges='four old/new source-only standard-axiom reports REUSED; guards strict public type checked here',AdapterRwAccepted='same97caa source old38328c… to new2af727…; source/kernel/2 standard-axiom reports REUSED, owner type equality remains qualified alpha, no old Accepted raw in baseline'),
 provenance_audit_revision='final: source-only correction maps M31/CM31/QM31 type declarations and generated field/constructor names to Types; Funs owns functions and their private helpers; v1 artifacts retained externally',
 newer_source_selected_three='acee18588f source-only report read; its three new modules require subsequent explicit raw delta or coherent replay; not attributed to103484b3c83b release',
 artifacts=newpins,axioms='N/A: raw IO and noncompiler data audit',budget=dict(local_diagnostics_used=3,local_max=3,old_failures_retained=True,global_actual=352,global_ceiling=368,remaining=16,unassigned=4,here=0,reserved_consumers=5,formerPort24=7),
 security='BOTH TARGETS NOT YET ESTABLISHED; ALL14/child/event/mark/native/source/artifact and SDK/Std/runtime/allocator/extraction boundaries OPEN',
 wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(0).ru_maxrss,swaps=resource.getrusage(0).ru_nswap,exit_status=0)
assert summary['peak_rss_bytes']<512*1024**2
write(E/'Port29SDKDATA_Strict-v3-final-audit.json',summary)
print(json.dumps({k:summary[k] for k in ['prior54','graph','new_transports','current_release_duplicates','further_variant_worklist','wall_seconds','peak_rss_bytes']}))
