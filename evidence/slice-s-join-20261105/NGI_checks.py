"""Additional independent gates; historical validators remain unchanged."""
STD={'propext','Classical.choice','Quot.sound'}
def check(a,scan,manifest,cert,inventory,entries,modules,delta):
 names=[r['root'] for r in a['results']]
 assert len(names)==len(set(names))==len(manifest['roots']) and set(names)==set(manifest['roots'])
 assert a['headline']==manifest['headline']=='AspisR1.RPx_Deployed.deployed'
 assert all(set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD for r in a['results'])
 assert len(a['fixtures'])==8 and all(r['equal'] for r in a['fixtures'])
 assert all(r['walked_axioms'] for r in a['fixtures'][:4]) and all(not r['walked_axioms'] for r in a['fixtures'][4:])
 assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] is True for r in scan)
 assert {'RPx_Deployed','NFX_COMBINED_IMPORT','NFY_COMBINED_IMPORT','NGE_COMBINED_IMPORT','NGF_COMBINED_IMPORT','NGI_COMBINED_IMPORT'}<={r['module'] for r in scan}
 assert a['walker_conformance']['byte_identical'] and a['same_proof_binary']['sha256']
 assert len(inventory)==cert['all_S_occurrences']==cert['selected_certificates']==97
 assert len({r['row'] for r in inventory})==97
 expected_names={t['canonical_name'] for r in inventory for t in r['theorems']}
 assert len(expected_names)==261 and set(entries)==expected_names and expected_names<=set(names)
 assert cert['theorem_record_occurrences']==sum(len(r['theorems']) for r in inventory)==19364
 for r in inventory:
  for t in r['theorems']:
   e=entries[t['canonical_name']];assert e['found'] is True and e['is_theorem'] is True
   assert e['module_idx'] is not None and modules[e['module_idx']]==t['canonical_module']
 assert cert['missing_or_wrong_owner']==[] and cert['not_name_filtered'] is True
 assert delta['inventory_rows']==599 and delta['inventory_identity_unchanged'] is True
 assert delta['S_after']=={'CLOSED':97} and delta['S_roots_CLOSED']==7 and len(delta['S_roots'])==7
 assert all(r['status']=='CLOSED' for r in delta['S_roots']) and delta['remaining_qualified_S']==[]
 assert len(delta['promotions'])==14 and delta['selected_callee_denial_propagation'] is True
 assert delta['new_trust_rows']==delta['removed_trust_rows']==[] and delta['cold_release_replay'] is False and delta['security_target_established'] is False
 return True

def propagate(rows):
 while True:
  denied={c for r in rows if r['composed_status']!='CLOSED' for c in r['selected_claims']};accepted={c for r in rows if r['composed_status']=='CLOSED' for c in r['selected_claims']};changed=False
  for r in rows:
   if r['composed_status']=='CLOSED' and any(c in denied and c not in accepted for o in r['caller_domain_obligations'] for c in o.get('callee_claims',[])):
    r['composed_status']='QUALIFIED';changed=True
  if not changed:return
