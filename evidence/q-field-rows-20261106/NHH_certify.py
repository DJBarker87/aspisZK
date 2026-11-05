from pathlib import Path
import json,lzma,hashlib,runpy,copy,collections,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):
 p=Path(p)
 return json.loads(p.read_bytes() if p.exists() else lzma.decompress(Path(str(p)+'.xz').read_bytes()))
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
base=J(R/'evidence/ledger9-20261105/NGZ_LEDGER.json');sets=J(R/'evidence/ledger9-20261105/NGZ_SLICES.json');targets=J(E/'NHH_TARGETS.json')['rows'];b={r['row']:r for r in base['rows']}
# Execute the inherited refresh gate without changing its predicates or outputs.
old=runpy.run_path(str(R/'evidence/ledger9-20261105/NGZ_validate.py'))
old['gate'](base,J(R/'evidence/ledger9-20261105/NGZ_AUDIT.json'),J(R/'evidence/ledger9-20261105/NGZ_SCAN.json'),J(R/'evidence/ledger9-20261105/NGZ_TRUST_USED.json'),J(R/'evidence/ledger9-20261105/NGZ_L003-admission.json'))
review=E/'NHH_review';summary=J(review/'SUMMARY.json');assert summary['status']=='PASS'
results=[x for r in summary['commands'] if r['target'].startswith('proof') for x in r['results']];fixtures=J(review/'fixtures.json')['results'];scan=J(review/'SCAN_SUMMARY.json')
roots=J(E/'NHH_AUDIT_ROOTS.json')['roots'];assert {x['root'] for x in results}==set(roots)
assert len(fixtures)==8 and all(x['equal'] for x in fixtures)
assert all(set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} and x['equal'] for x in results)
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
put('NHH_AUDIT.json',dict(status='PASS',headline='AspisR1.RPx_Deployed.deployed',results=results,fixtures=fixtures,scan=scan,receipt='NHH_L007/receipt.json',raw_authoritative=True,cold_release_replay=False))
configs=[('m31_embed',7,8,'base'),('cm31_embed',9,10,'complex'),('qm31_embed',11,12,'quadratic'),('wide_embed',13,14,'wide'),('cm_inherent',15,16,'inherent')]
functions=[]
for harness,pos,neg,lemma in configs:
 domain='every raw u32 input, no canonicality or successful-return premise'
 fs={'base':'crates/aspis-core/src/r0/scalar.rs::M31::from_m31','complex':'crates/aspis-core/src/r0/scalar.rs::CM31::from_m31','quadratic':'crates/aspis-core/src/r0/scalar.rs::QM31::from_m31','wide':'crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31','inherent':'crates/aspis-core/src/field.rs::CM31::from_m31'}
 f=fs[lemma];rs=[r['row'] for r in targets if r['function']==f];assert rs
 functions.append(dict(function=f,rows=rs,status='CLOSED',form='ordinary (y) direct full immutable native constructor and emitted-body totality',domain=domain,native_positive=f'NHH_K{pos:03}',matched_control=f'NHH_K{neg:03}',copy_pair=['NHH_K019','NHH_K020'],model_root='NHH_Embedding.'+lemma,domain_root='NHH_Embedding.canonical',cohort_association='NHH_Embedding.accumulation',frame='Complete returned scalar/record; no mutated input, no effects',callee_domains='M31 trait accepts every word; normalized outputs canonical; inherent CM31 embedding accepts every word; all actual callees execute in native checks',trust='P6/D188 option A retained/reclassified; no new trust'))
closed=[rid for f in functions for rid in f['rows']];assert len(closed)==9
native=[]
for k in list(range(7,17))+[19,20]:
 a=f'NHH_K{k:03}';rc=J(E/a/'receipt.json');g=J(E/(a+'-graph-check.json'));lock=J(E/(a+'-lock-check.json'));cfg=J(E/(a+'.json'));ad=J(E/(a+'-admission.json'));s=(E/a/'stdout.log').read_text();neg=k in [8,10,12,14,16,20]
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert g['graph_matches_frozen'] and not g['edge_errors'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert rc['exit_status']==(1 if neg else 0) and ('VERIFICATION:- FAILED' if neg else 'VERIFICATION:- SUCCESSFUL') in s and 'Timed out' not in s
 assert cfg['env']['CARGO_NET_OFFLINE']=='true';assert '--cfg NHH_invert' in cfg['env']['RUSTFLAGS'] if neg else '--cfg NHH_invert' not in cfg['env']['RUSTFLAGS']
 native.append(dict(attempt=a,exit=rc['exit_status'],verdict='matched assertion failure' if neg else 'PASS',source_pins=H((E/'NHH_SOURCE_PINS.json').read_bytes()),frozen_graph=True,unchanged_lock=True))
put('NHH_NATIVE_VALIDATION.json',dict(status='PASS',attempts=native,suspended=[],quarantined=[]))
put('NHH_CLOSED.json',dict(schema_version=1,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',new_composed_functions=5,new_composed_rows=9,functions=functions,headline_target_established=False,trust_removed=False))
edges=[]
for f in functions:
 for child in sorted(set(c for rid in f['rows'] for c in b[rid]['canonical_callees'])):
  assert child in [q['function'] for q in functions] or any(r['function']==child and r['composed_status']=='CLOSED' for r in base['rows']),child
  edges.append(dict(caller=f['function'],callee=child,status='CLOSED',argument_domain='SAME raw input for trait child; normalized result canonical for enclosing embedding; inherent from_cm31/from_qm31 domains established by total reduction',proof=f['model_root'],native=f['native_positive']))
put('NHH_EDGES.json',dict(edges=edges,new_closed_edges=len(edges)))
put('NHH_LEDGER_DELTA.json',dict(baseline='evidence/ledger9-20261105/NGZ_LEDGER.json.xz',baseline_raw_sha256=H(lzma.decompress((R/'evidence/ledger9-20261105/NGZ_LEDGER.json.xz').read_bytes())),slice='Q',inventory_rows=599,new_closed_rows=closed,new_functions=5,validator_checks_added_only=True,no_other_status_change=True,retained_trust=True,baseline_gate_sha256=H((R/'evidence/ledger9-20261105/NGZ_validate.py').read_bytes()),pending=[dict(row=r['row'],function=r['function'],status='OPEN',reason='Native/model/canonical caller composition remains incomplete; native fragment alone is not promoted') for r in targets if r['row'] not in closed]))
reverse=collections.defaultdict(set)
for r in base['rows']:
 for c in r['canonical_callees']:reverse[c].add(r['function'])
lines=['# NHH slice-boundary consumers','','Only explicit source-graph reachability is listed. A closed field row does not close an enclosing driver.','']
for f in functions:
 seen=set();todo=[f['function']]
 while todo:
  n=todo.pop()
  for c in reverse[n]:
   if c not in seen:seen.add(c);todo.append(c)
 drivers=sorted(n for n in seen if any(s in n for s in ['verifier.rs::Prepared::new','candidate.rs::prepare','candidate.rs::tx1','verifier.rs::finish_relation','candidate.rs::tx2_common','r1_semantic.rs::verify_observed','lib.rs::process_r1_cost_probe_instruction','transcript.rs::Transcript<H>::queries','r0/scalar.rs::']))
 lines+=['## '+f['function'],'','Rows: '+', '.join(f['rows'])+'.','', 'Immediate consumers: '+('; '.join(sorted(reverse[f['function']])) or '(none in conservative inventory)')+'.','', 'Driver cones reached: '+('; '.join(drivers) or '(none selected by named driver filter)')+'.','']
(E/'NHH_CONSUMERS.md').write_text('\n'.join(lines))
print(json.dumps(dict(status='PASS',new_rows=closed,new_edges=len(edges),audit_roots=len(results),scan_modules=scan['modules'])))
