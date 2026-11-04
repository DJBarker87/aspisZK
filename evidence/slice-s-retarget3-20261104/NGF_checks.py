"""Independent additive certificate/coherence admission; never waive history."""
STD={'propext','Classical.choice','Quot.sound'}
HEADLINE='AspisR1.RPx_Deployed.deployed'
def check_bundle(a,scan,manifest):
 assert a['headline']==manifest['headline']==HEADLINE
 actual=[r['root'] for r in a['results']];assert len(actual)==len(set(actual))==len(manifest['roots']) and set(actual)==set(manifest['roots'])
 assert a['root_count']==len(actual)
 for r in a['results']:
  assert set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD
  assert r['parent_attempt'] and r['source_revision'] and r['uncompressed_sha256'] and r['compressed_sha256']
 fixtures=a['fixtures'];assert len(fixtures)==8 and len({r['root'] for r in fixtures})==8 and all(r['equal'] for r in fixtures)
 assert all(r['walked_axioms'] for r in fixtures[:4]) and all(not r['walked_axioms'] for r in fixtures[4:])
 assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] is True for r in scan)
 mods={r['module'] for r in scan};assert {'RPx_Deployed','NFY_COMBINED_IMPORT','NGF_COMBINED_IMPORT'}<=mods
 assert not ({'S1SemanticPhaseV1','PreparedFromQmSourceBridge','ExtractedTx1Reachability'}&mods)
 assert a['walker_conformance']['byte_identical'] is True and a['same_proof_binary']['sha256']
 return True

def check_delta(base,nfy,d,cert,inventory,scan,prov):
 import collections,copy
 rows=copy.deepcopy(base['rows']);by={r['row']:r for r in rows};reviewed={r['row'] for r in rows if r['composed_status']=='QUALIFIED'}
 assert len(reviewed)==89 and set(d['reviewed_S_rows'])==reviewed
 cr={r['row']:r for r in cert['rows']};inv={r['row']:r for r in inventory};assert set(cr)==set(inv)==reviewed
 mods={r['module'] for r in scan};expected_gaps=set()
 for rid in reviewed:
  c=cr[rid];i=inv[rid];assert c['certificate_sha256']==i['certificate_sha256'] and c['records']==len(i['theorems'])==len(c['theorems'])
  # Compare every record in original traversal order, including duplicate uses.
  for original,t in zip(i['theorems'],c['theorems']):
   for k,v in original.items():assert t[k]==v,('changed certificate record',rid,k)
   loaded=t['canonical_module'] in mods
   assert t['loaded_and_raw_audited']==loaded
   if not loaded:expected_gaps.add((rid,t['canonical_name'],t['canonical_module']))
  assert c['all_named_declarations_loaded']==all(t['loaded_and_raw_audited'] for t in c['theorems'])
 assert cert['theorem_record_occurrences']==sum(len(r['theorems']) for r in inventory)
 assert expected_gaps=={(g['row'],g['canonical_name'],g['unloaded_module']) for g in cert['gaps']}
 assert cert['not_name_filtered'] is True and cert['chain_B_missing']==[]
 assert not any(g['unloaded_module'] in {r['target_module'] for r in prov['files']} for g in cert['gaps'])
 direct={g['row'] for g in cert['gaps']};prior={r['row'] for r in nfy['promotions']}
 for rid in prior:by[rid]['composed_status']='CLOSED'
 before=dict(collections.Counter(r['composed_status'] for r in rows));before['OPEN']+=12;assert d['before']==before
 for rid in reviewed-direct:by[rid]['composed_status']='CLOSED'
 while True:
  denied={c for r in rows if r['composed_status']!='CLOSED' for c in r['selected_claims']};accepted={c for r in rows if r['composed_status']=='CLOSED' for c in r['selected_claims']};changed=False
  for r in rows:
   if r['composed_status']=='CLOSED' and any(c in denied and c not in accepted for o in r['caller_domain_obligations'] for c in o.get('callee_claims',[])):
    r['composed_status']='QUALIFIED';changed=True
  if not changed:break
 expected={rid for rid in reviewed-prior if by[rid]['composed_status']=='CLOSED'}
 assert {r['row'] for r in d['promotions']}==expected
 assert {r['row'] for r in d['remaining_qualified_S']}=={rid for rid in reviewed if by[rid]['composed_status']!='CLOSED'}
 for r in d['promotions']:
  assert r['function']==by[r['row']]['function'] and r['frozen_body_sha256']==by[r['row']]['frozen_body_sha256']
  assert r['before']=='QUALIFIED' and r['after']=='CLOSED'
 after=dict(collections.Counter(r['composed_status'] for r in rows));after['OPEN']+=12;assert d['after']==after and d['inventory_rows']==599
 assert d['new_trust_rows']==[] and d['removed_trust_rows']==[] and d['security_target_established'] is False and d['cold_release_replay'] is False
 return True
