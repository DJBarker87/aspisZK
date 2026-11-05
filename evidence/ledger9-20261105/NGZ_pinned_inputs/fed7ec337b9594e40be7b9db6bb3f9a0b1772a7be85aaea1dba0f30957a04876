"""Additive evidence gates; all historical validators remain unchanged."""
STD={'propext','Classical.choice','Quot.sound'}
HEADLINE='AspisR1.RPx_Deployed.deployed'
def check_bundle(audit,scan,manifest):
 assert audit['headline']==manifest['headline']==HEADLINE
 expected=manifest['roots'];actual=[r['root'] for r in audit['results']]
 assert len(actual)==len(set(actual))==len(expected) and set(actual)==set(expected)
 assert audit['root_count']==len(expected)
 for r in audit['results']:
  assert set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD
  assert r['parent_attempt'] and r['source_revision'] and r['uncompressed_sha256'] and r['compressed_sha256']
 fixtures=audit['fixtures'];assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
 assert len({r['root'] for r in fixtures})==8
 assert all(r['walked_axioms'] for r in fixtures[:4]) and all(not r['walked_axioms'] for r in fixtures[4:])
 assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] is True for r in scan)
 modules={r['module'] for r in scan};assert 'NFY_COMBINED_IMPORT' in modules and 'RPx_Deployed' in modules
 assert not ({'S1SemanticPhaseV1','PreparedFromQmSourceBridge','ExtractedTx1Reachability'}&modules)
 assert audit['walker_conformance']['byte_identical'] is True
 return True

def check_delta(baseline,delta,gaps,certificates,scan):
 import copy,collections
 rows=copy.deepcopy(baseline['rows']);by={r['row']:r for r in rows};reviewed={r['row'] for r in rows if r['composed_status']=='QUALIFIED'}
 assert len(reviewed)==89 and set(delta['reviewed_S_rows'])==reviewed
 modules={r['module'] for r in scan};cr={r['row']:r for r in certificates['rows']};assert set(cr)==reviewed
 expected_gaps={(r['row'],t['canonical_name'],t['canonical_module']) for r in cr.values() for t in r['canonical_theorem_associations'] if t['canonical_module'] not in modules}
 assert expected_gaps=={(g['row'],g['canonical_name'],g['unloaded_module']) for g in gaps}
 direct={g['row'] for g in gaps}
 for rid in reviewed:
  assert cr[rid]['frozen_body_sha256']==by[rid]['frozen_body_sha256']
  if rid not in direct:by[rid]['composed_status']='CLOSED'
 while True:
  denied={c for r in rows if r['composed_status']!='CLOSED' for c in r['selected_claims']};accepted={c for r in rows if r['composed_status']=='CLOSED' for c in r['selected_claims']};changed=False
  for r in rows:
   if r['composed_status']=='CLOSED' and any(c in denied and c not in accepted for o in r['caller_domain_obligations'] for c in o.get('callee_claims',[])):
    r['composed_status']='QUALIFIED';changed=True
  if not changed:break
 expected={rid for rid in reviewed if by[rid]['composed_status']=='CLOSED'}
 assert {r['row'] for r in delta['promotions']}==expected
 assert {r['row'] for r in delta['remaining_qualified_S']}==reviewed-expected
 for p in delta['promotions']:
  assert p['function']==by[p['row']]['function'] and p['frozen_body_sha256']==by[p['row']]['frozen_body_sha256']
  assert p['before']=='QUALIFIED' and p['after']=='CLOSED'
 assert delta['after']==dict(collections.Counter(r['composed_status'] for r in rows))
 assert delta['new_trust_rows']==[] and delta['removed_trust_rows']==[]
 assert delta['security_target_established'] is False and delta['cold_release_replay'] is False
 return True
