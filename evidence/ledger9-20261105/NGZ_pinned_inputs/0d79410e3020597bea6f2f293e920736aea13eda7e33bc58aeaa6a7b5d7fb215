"""Additive gates on the complete selected-certificate inventory."""
import copy,collections
STD={'propext','Classical.choice','Quot.sound'}
def check_bundle(audit,scan,manifest,certs,prov):
 assert audit['headline']==manifest['headline']=='AspisR1.RPx_Deployed.deployed'
 assert audit['walker_conformance']['byte_identical'] is True
 roots=[r['root'] for r in audit['results']];expected=manifest['roots'];assert len(roots)==len(set(roots))==len(expected) and set(roots)==set(expected)
 assert [n for g in manifest['groups'] for n in g]==expected
 for r in audit['results']:
  assert set(r['walked_axioms'])<=STD and set(r['collect_axioms'])<=STD
  assert r['parent_attempt'] and r['source_revision'] and r['compressed_sha256'] and r['uncompressed_sha256']
 fixtures=audit['fixtures'];assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
 assert len({r['root'] for r in fixtures})==8
 assert all(r['walked_axioms'] for r in fixtures[:4]) and all(not r['walked_axioms'] for r in fixtures[4:])
 assert len(set(audit['proof_driver_binary_sha256']))==1
 assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] is True for r in scan)
 mods={r['module'] for r in scan};assert {'RPx_Deployed','NFX_COMBINED_IMPORT','NFY_COMBINED_IMPORT','NGE_COMBINED_IMPORT'}<=mods
 assert not {'S1SemanticPhaseV1','PreparedFromQmSourceBridge','ExtractedTx1Reachability'}&mods
 assert {'NGE_'+n for n in prov['order']}<=mods
 assert {q['canonical_name'] for r in certs['rows'] for q in r['theorems'] if q['canonical_module'] in mods}<=set(roots)
 return True

def derive(baseline,certs,mods):
 rows=copy.deepcopy(baseline['rows']);reviewed={r['row'] for r in certs['rows']};by={r['row']:r for r in rows};causes={};gaps=[]
 assert len(reviewed)==89 and reviewed=={r['row'] for r in rows if r['composed_status']=='QUALIFIED'}
 for r in certs['rows']:
  for t in r['theorems']:
   if t['canonical_module'] not in mods:gaps.append(dict(row=r['row'],canonical_name=t['canonical_name'],canonical_module=t['canonical_module'],legacy_name=t['legacy_name'],source=t['source']))
 direct={r['row'] for r in gaps}
 for rid in reviewed:
  if rid not in direct:by[rid]['composed_status']='CLOSED'
  else:causes[rid]=dict(kind='missing_auxiliary_certificate_declaration',gaps=[g for g in gaps if g['row']==rid])
 while True:
  denied={c for r in rows if r['composed_status']!='CLOSED' for c in r['selected_claims']};accepted={c for r in rows if r['composed_status']=='CLOSED' for c in r['selected_claims']};changed=False
  for r in rows:
   if r['composed_status']!='CLOSED':continue
   bad=sorted({c for o in r['caller_domain_obligations'] for c in o.get('callee_claims',[]) if c in denied and c not in accepted})
   if bad:r['composed_status']='QUALIFIED';causes[r['row']]=dict(kind='qualified_selected_callee',claims=bad);changed=True
  if not changed:break
 return rows,gaps,causes

def check_delta(base,prior,delta,certs,scan):
 rows,gaps,causes=derive(base,certs,{r['module'] for r in scan});by={r['row']:r for r in rows};old_closed={p['row'] for p in prior['promotions']}
 newly={r['row'] for r in certs['rows'] if by[r['row']]['composed_status']=='CLOSED'}-old_closed
 assert {p['row'] for p in delta['promotions']}==newly
 assert {r['row'] for r in delta['remaining_qualified_S']}=={r['row'] for r in certs['rows'] if by[r['row']]['composed_status']!='CLOSED'}
 for p in delta['promotions']:
  assert p['before']=='QUALIFIED' and p['after']=='CLOSED'
  assert p['function']==by[p['row']]['function'] and p['frozen_body_sha256']==by[p['row']]['frozen_body_sha256']
 for r in delta['remaining_qualified_S']:assert r['reason']==causes[r['row']]
 assert delta['inventory_basis']==599 and delta['historical_NFX_basis']==587
 assert delta['new_trust_rows']==delta['removed_trust_rows']==[]
 assert delta['security_target_established'] is False and delta['cold_release_replay'] is False
 return True
