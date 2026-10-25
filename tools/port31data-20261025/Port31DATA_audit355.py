#!/usr/bin/env python3
"""Streaming, bounded355 audit. No compiler or logical acceptance."""
import collections,json,pathlib,resource,sqlite3,subprocess,time
from Port31DATA_run import T,E,pin,state,safe
start=time.monotonic();receipt=E/'Port31DATA_attempt-355.json';rec=json.loads(receipt.read_text());out=pathlib.Path(rec['env']['PORT31_DATA']);raw=out/'Port31DATA_raw355.jsonl'
def key(x):return json.dumps(x,separators=(',',':'),ensure_ascii=False)
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
before=state(safe(raw));assert pin(raw)==next(x for x in rec['outputs'] if x['path']==str(raw))
dbpath=out/'Port31DATA_inventory355.sqlite';assert not dbpath.exists();db=sqlite3.connect(dbpath)
db.executescript('PRAGMA cache_size=-12000; PRAGMA mmap_size=0; CREATE TABLE constant(name TEXT,origin TEXT,display TEXT,kind TEXT,unsafe INTEGER,partial INTEGER,value INTEGER,info TEXT); CREATE TABLE reached(name TEXT PRIMARY KEY,origins TEXT); CREATE TABLE pair(name TEXT,left_origin TEXT,right_origin TEXT,strict INTEGER,strict_type INTEGER,strict_value INTEGER,strict_rules INTEGER);')
counts=collections.Counter();exports=[];guards=[];bools=[];apps=[];owner=[];covered=[];coreparts=[];s8=[];summary=None;groups=[]
with raw.open() as f:
 for line in f:
  r=json.loads(line);tag=r['tag'];counts[tag]+=1
  if tag=='constant':
   c=r['constant'];db.execute('INSERT INTO constant VALUES(?,?,?,?,?,?,?,?)',(key(c['name']),r['origin'],c['display'],c['kind'],c['unsafe'],c['partial'],c['has_value'],key(c)))
   if r['origin'].startswith('S8:'):s8.append(dict(origin=r['origin'],**c))
  elif tag=='reached':db.execute('INSERT INTO reached VALUES(?,?)',(key(r['name']),key(r['origins'])))
  elif tag=='pair':db.execute('INSERT INTO pair VALUES(?,?,?,?,?,?,?)',(key(r['name']),r['left'],r['right'],r['strict'],r['strict_type'],r['strict_value'],r['strict_rules']))
  elif tag in ['guard','name-guard']:guards.append(r)
  elif tag=='bool-body':bools.append(r)
  elif tag=='historical-bool-application':apps.append(r)
  elif tag=='summary':assert summary is None;summary=r
  elif tag=='export':exports.append(r)
  elif tag=='part' and r['origin'].startswith('CORE:'):coreparts.append(r)
  elif tag=='owner43-pair':owner.append(r)
  elif tag=='owner43-covered':covered.append(r)
  elif tag=='group':groups.append(r)
db.executescript('CREATE INDEX by_name ON constant(name); CREATE INDEX pair_name ON pair(name); CREATE INDEX by_display ON constant(display);');db.commit()
# All source groups are preserved independently; no main/server body replacement.
expected={'S8:S8OwnedP6:part0','S8:S8OwnedP6Foundations:part0','BOOL:NEW-PROOF:part0','CORE:Init.Core:part0','CORE:Init.Core:part1','CORE:Init.Core:part2'}
actual={r['origin'] for r in exports}
# Release labels are derived from the explicit two-object release, not assumed.
inputplan=json.loads((E/'Port31DATA_next-inputs355.json').read_text())
expected={g['label']+':part'+str(i) for g in inputplan['groups'] if g['kind'] in ['OWN','CORE'] for i in range(len(g['paths']))}
assert len(expected)==6
exportpins=[]
for r in exports:
 p=pin(safe(r['path']));assert p in rec['outputs'];exportpins.append(p)
complete=(rec['accepted'] and summary is not None and actual==expected and len(exports)==6 and all(r['strict_source_part_readback'] for r in exports) and len(covered)==43 and {r['id'] for r in covered}=={str(i) for i in range(43)} and all(not r['strict'] and r['reflexive'] for r in guards if r['tag']=='guard') and counts['guard']==5 and counts['group']==1917 and counts['part']==1919)
# Do independent complete body/group closure for all S8 constants, not only roots.
seen=set();todo=[key(r['name']) for r in s8];gaps=set()
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);cs=list(db.execute('SELECT info FROM constant WHERE name=?',(n,)))
 if not cs:gaps.add(n);continue
 for (info,) in cs:
  todo.extend(key(d) for d in json.loads(info)['dependencies'] if key(d) not in seen)
selection=out/'Port31DATA_selection355.jsonl';modes=collections.Counter();rejects=collections.Counter();placeholders=set();conflicts=0;proofvariants=0;partialnames=[]
with selection.open('x') as f:
 for n,origins in db.execute('SELECT name,origins FROM reached ORDER BY name'):
  rows=list(db.execute('SELECT origin,kind,unsafe,partial,value,info FROM constant WHERE name=? ORDER BY origin',(n,)))
  ps=list(db.execute('SELECT left_origin,right_origin,strict,strict_type,strict_value,strict_rules FROM pair WHERE name=?',(n,)))
  eligible=[];variants=[]
  for origin,kind,unsafe,partial,value,info in rows:
   c=json.loads(info);why=[]
   if unsafe:why.append('unsafe')
   if partial:why.append('partial')
   if kind=='axiom' and c['display'] not in ['propext','Classical.choice','Quot.sound']:why.append('nonstandard-axiom-or-placeholder')
   if kind in ['definition','theorem','opaque'] and not value:why.append('missing-full-body')
   if kind=='axiom' and any(r[1] in ['definition','theorem','opaque'] and r[4] for r in rows):placeholders.add(n)
   for w in why:rejects[w]+=1
   if not why:eligible.append(origin)
   variants.append(dict(origin=origin,logical_rejection=why,complete_record=c))
  if not rows:status='missing-input'
  elif not eligible:status='no-safe-logical-seed'
  elif len(rows)==1:status='single-safe-candidate-needs-kernel'
  elif all(p[2] for p in ps):status='strict-equivalence-class-needs-explicit-kernel-selection'
  else:status='conflicting-variants-explicit-selection-required';conflicts+=1
  proofvariants+=sum(not p[2] and p[3] and not p[4] for p in ps)
  modes[status]+=1
  f.write(key(dict(name=json.loads(n),status=status,chosen_origin=None,kernel_rechecked=False,safe_candidate_choices=eligible,variants=variants,strict_pair_receipts=[dict(left=p[0],right=p[1],strict=bool(p[2]),strict_type=bool(p[3]),strict_value=bool(p[4]),strict_rules=bool(p[5])) for p in ps]))+'\n')
# Preserve historical13 and all historical representation/proof variants untouched.
hist=E/'Port31DATA_reused-variant-obligations.json';historical=json.loads(hist.read_text())['historical_data'];old13=historical['conflicting13']
conflict_inventory=[]
for display in old13:
 rows=list(db.execute('SELECT name,origin,info FROM constant WHERE display=? ORDER BY origin',(display,)))
 conflict_inventory.append(dict(presentation_label=display,variants=[dict(name=json.loads(n),origin=o,info=json.loads(c)) for n,o,c in rows],selection='NONE; historical conflict retained'))
enums=[]
for display in ['noConfusionTypeEnum','noConfusionEnum']:
 enums.append(dict(display=display,core_variants=[dict(name=json.loads(n),origin=o,kind=k,has_value=bool(v)) for n,o,k,v in db.execute("SELECT name,origin,kind,value FROM constant WHERE display=? AND origin LIKE 'CORE:%'",(display,))]))
full_enum=all(any(c['has_value'] and c['kind']=='definition' for c in r['core_variants']) for r in enums)
complete=complete and full_enum
report=dict(status='ACCEPTED RAW DATA/STRICT READBACK ONLY' if complete else 'INCOMPLETE/FAILED355; ALL OUTPUTS QUARANTINED',accepted_data=complete,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),command=['python3','-B',str(pathlib.Path(__file__))],source=pin(__file__),receipt=pin(receipt),input=pin(raw),events=dict(counts),print_axioms='N/A: raw IO, no theorem; Bool353 original NO AXIOMS audit REUSED',new_lean_invocations=0,global_actual=355,global_ceiling=368,remaining=dict(unassigned=1,reserved_kernel_consumers=5,carry=7,total=13),exports=dict(expected_origins=sorted(expected),observed=exports,pins=exportpins,source_pin_assessment='S8 freshly pinned release bytes; Core original historical hashes reused with exact safe/stat continuity; new export hashes fresh'),guards=guards,owner43=dict(covered_rows=len(covered),pair_count=len(owner),strict_true=sum(r['strict'] for r in owner),strict_false=sum(not r['strict'] for r in owner),rows=covered,pairs=owner),core=dict(original_parts=coreparts,enum_helpers=enums,full_enum_bodies_observed=full_enum,not_last_dependencies_claimed=True),s8=dict(constants=len(s8),kinds=dict(collections.Counter(r['kind'] for r in s8)),all_actual_Name_seed_union=dict(reached=len(seen),gaps=[json.loads(n) for n in sorted(gaps)])),three_root_union=summary,selection=dict(status_counts=dict(modes),no_selected_origin=True,placeholder_fullbody_names=len(placeholders),conflicting_names=conflicts,strict_type_equal_value_variant_pair_observations=proofvariants,rejections=dict(rejects),policy='Only listed safe candidates may be considered; none chosen. Strict-equal classes need explicit kernel selection; differing variants require per-origin policy, never firstwins; all raw groups preserved.'),historical_reuse=dict(pin=pin(hist),thirteen_conflicts=conflict_inventory,assessment='Historical13/45/proof differences retained; not automatically discharged'),bool_compatibility=dict(bodies=bools,historical_applications=apps,requirement='Later ordinary kernel consumer must check exact alias/shim and original application; new Bool is namespaced, not old helper identity'),outputs=[pin(dbpath),pin(selection)],source_pre_post_unchanged=state(raw)==before,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,exit_status=0,security_targets='BOTH NOT ESTABLISHED')
assert report['source_pre_post_unchanged']
write(E/'Port31DATA_audit355.json',report)
print(json.dumps(dict(status=report['status'],events=dict(counts),s8=report['s8'],owner43={k:report['owner43'][k] for k in ['covered_rows','pair_count','strict_true','strict_false']},selection=report['selection'],reached=None if summary is None else summary['reached'],gaps=None if summary is None else summary['gaps'],wall_seconds=report['wall_seconds'])))
