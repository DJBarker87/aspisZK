#!/usr/bin/env python3
"""Bounded analysis of FAILED attempt354 data. Never promotes it to accepted evidence."""
import collections,hashlib,json,pathlib,resource,sqlite3,subprocess,time
from Port31DATA_run import T,E,pin,state,safe
start=time.monotonic();rec=json.loads((E/'Port31DATA_attempt-354.json').read_text());out=pathlib.Path(rec['env']['PORT31_DATA'])
raw=out/'Port31DATA_raw.jsonl';before=state(safe(raw));assert pin(raw)==next(x for x in rec['outputs'] if x['path']==str(raw))
dbpath=out/'Port31DATA_observed.sqlite';assert not dbpath.exists()
db=sqlite3.connect(dbpath);db.executescript('PRAGMA cache_size=-12000; PRAGMA mmap_size=0; CREATE TABLE constant(name TEXT,origin TEXT,display TEXT,kind TEXT,unsafe INTEGER,partial INTEGER,value INTEGER,info TEXT); CREATE TABLE reached(name TEXT PRIMARY KEY,origins TEXT); CREATE TABLE pair(name TEXT,left_origin TEXT,right_origin TEXT,strict INTEGER,strict_type INTEGER,strict_value INTEGER,strict_rules INTEGER);')
def key(x):return json.dumps(x,separators=(',',':'),ensure_ascii=False)
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
counts=collections.Counter();s8=[];guards=[];bools=[];app=[];summary=None;exports=[];parts=[]
with raw.open() as f:
 for line in f:
  r=json.loads(line);tag=r['tag'];counts[tag]+=1
  if tag=='constant':
   c=r['constant'];n=key(c['name']);db.execute('INSERT INTO constant VALUES(?,?,?,?,?,?,?,?)',(n,r['origin'],c['display'],c['kind'],c['unsafe'],c['partial'],c['has_value'],key(c)))
   if r['origin'].startswith('S8:'):s8.append(dict(origin=r['origin'],**c))
  elif tag=='reached':db.execute('INSERT INTO reached VALUES(?,?)',(key(r['name']),key(r['origins'])))
  elif tag=='pair':db.execute('INSERT INTO pair VALUES(?,?,?,?,?,?,?)',(key(r['name']),r['left'],r['right'],r['strict'],r['strict_type'],r['strict_value'],r['strict_rules']))
  elif tag=='guard' or tag=='name-guard':guards.append(r)
  elif tag=='fresh-bool-body':bools.append(r)
  elif tag=='historical-bool-application':app.append(r)
  elif tag=='summary':summary=r
  elif tag=='export':exports.append(r)
  elif tag=='part' and r['origin'].startswith('S8:'):parts.append(r)
db.executescript('CREATE INDEX by_name ON constant(name); CREATE INDEX pair_name ON pair(name); CREATE INDEX by_display ON constant(display);');db.commit()
# Fresh supplemental body-shape graph: actual107 S8 Name objects as seeds, not printed labels.
# This remains unaccepted raw diagnostic output; it is not a kernel or export-readback result.
seen=set();todo=[key(r['name']) for r in s8];gaps=set()
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);cs=list(db.execute('SELECT info FROM constant WHERE name=?',(n,)))
 if not cs:gaps.add(n);continue
 for (info,) in cs:
  for d in json.loads(info)['dependencies']:
   k=key(d)
   if k not in seen:todo.append(k)
# Preserve complete per-origin alternatives. No chosen_origin is invented.
selection=out/'Port31DATA_selection-preparation.jsonl';modes=collections.Counter();rejects=collections.Counter();placeholders=set();currentdup=[]
with selection.open('x') as f:
 for n,origins in db.execute('SELECT name,origins FROM reached ORDER BY name'):
  rows=list(db.execute('SELECT origin,kind,unsafe,partial,value,info FROM constant WHERE name=? ORDER BY origin',(n,)))
  ps=list(db.execute('SELECT left_origin,right_origin,strict,strict_type,strict_value,strict_rules FROM pair WHERE name=?',(n,)))
  allstrict=all(p[2] for p in ps);eligible=[];variants=[]
  for origin,kind,unsafe,partial,value,info in rows:
   c=json.loads(info);why=[]
   if unsafe:why.append('unsafe')
   if partial:why.append('partial')
   if kind=='axiom' and c['display'] not in ['propext','Classical.choice','Quot.sound']:why.append('nonstandard-axiom-or-abstract-placeholder')
   if kind in ['theorem','opaque','definition'] and not value:why.append('missing-full-body')
   if kind=='axiom' and any(r[1] in ['theorem','opaque','definition'] and r[4] for r in rows):placeholders.add(n)
   for w in why:rejects[w]+=1
   if not why:eligible.append(origin)
   variants.append(dict(origin=origin,kind=kind,unsafe=bool(unsafe),partial=bool(partial),has_value=bool(value),logical_rejection=why,complete_record=c))
  status='one-variant-pending-review' if len(rows)==1 else 'all-pairs-strict-equal-pending-explicit-selection' if allstrict else 'different-variants-explicit-selection-required'
  modes[status]+=1
  cp=[p for p in ps if p[0].startswith('CURRENT:') and p[1].startswith('CURRENT:')]
  if cp:currentdup.append(dict(name=json.loads(n),origins=json.loads(origins),pairs=len(cp),all_strict=all(p[2] for p in cp)))
  f.write(key(dict(name=json.loads(n),status=status,chosen_origin=None,kernel_rechecked=False,eligible_as_data_only=eligible,variants=variants,pair_guards=[dict(left=p[0],right=p[1],strict=bool(p[2]),strict_type=bool(p[3]),strict_value=bool(p[4]),strict_rules=bool(p[5])) for p in ps]))+'\n')
# Reuse historical conflicts and representation/proof differences explicitly.
old=json.loads(subprocess.check_output(['git','show','74a62fd7b6:evidence/port29sdkdata-20261025/Port29SDKDATA_Strict-v3-final-gaps.json']))
write(E/'Port31DATA_reused-variant-obligations.json',dict(source_revision='74a62fd7b6',source='Port29SDKDATA_Strict-v3-final-gaps.json',assessment='REUSED; not newly revalidated by failed354',historical_data=old))
oldgraph=json.loads(subprocess.check_output(['git','show','3bc1639:evidence/port30join-20261025/focused-graph.json']))
old35=[x for x in oldgraph['missing'] if x.startswith('S8OwnedP6.')]
observed={r['display'] for r in s8}
write(E/'Port31DATA_S8-observations.json',dict(status='UNACCEPTED raw observations from failed CLI; missing data NOT resolved',source_objects=[r for r in rec['outputs'] if '/raw/S8:' in r['path']],parts=parts,constant_count=len(s8),constant_kinds=dict(collections.Counter(r['kind'] for r in s8)),old35_display_correspondences_found=sorted(set(old35)&observed),old35_display_correspondences_absent=sorted(set(old35)-observed),actual_Name_group_delta=[r['name'] for r in s8 if r['display'] not in old35],constants=s8,supplemental_all107_exact_union=dict(reached=len(seen),gaps=[json.loads(n) for n in sorted(gaps)],kernel_ready=False,accepted=False),strict_source_part_readbacks=len(exports)))
write(E/'Port31DATA_Bool-body-observation.json',dict(ordinary_proof_receipt='Port31DATA_attempt-353.json',ordinary_proof_accepted=True,raw_observations=bools,original_application_observations=app,compatibility='semantic shape proved; historical implicit binder shape and body identity NOT established; no parse_header replay; no old-name alias'))
write(E/'Port31DATA_current-duplicates.json',dict(status='Runtime guard observations from FAILED diagnostic; not an accepted receipt',names=len(currentdup),all_strict=sum(x['all_strict'] for x in currentdup),data=currentdup))
assert state(raw)==before
report=dict(status='FAILED DIAGNOSTIC; retained observations only, NO body-closure or export-readback PASS',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=['python3','-B',str(pathlib.Path(__file__))],input=pin(raw),source=pin(__file__),diagnostic_receipt=pin(E/'Port31DATA_attempt-354.json'),events=dict(counts),guards=guards,three_roots_observed=summary,exact_name_selection_preparation=dict(status_counts=dict(modes),no_choices=True,logical_rejection_observations=dict(rejects),core_abstract_vs_full_name_count=len(placeholders),policy='retain all main/server abstract variants as DATA; select no nonstandard axiom; prefer no full-body variant without explicit re-pin or strict audit; future kernel guard required'),supplemental_S8_union=dict(seeds=len(s8),reached=len(seen),gap_count=len(gaps),gaps=[json.loads(n) for n in sorted(gaps)]),new_export_readback_receipts=len(exports),compiler_calls=0,global_actual=354,local_used=2,axioms='N/A: noncompiler raw-data processor',outputs=[pin(dbpath),pin(selection)],wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,exit_status=0,security_targets='NOT ESTABLISHED')
write(E/'Port31DATA_audit.json',report)
print(json.dumps({k:report[k] for k in ['status','events','three_roots_observed','exact_name_selection_preparation','supplemental_S8_union','wall_seconds','peak_rss_bytes']}))
