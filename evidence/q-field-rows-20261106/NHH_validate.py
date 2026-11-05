from pathlib import Path
import json,copy,hashlib,runpy,re,lzma
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda p:json.loads(Path(p).read_bytes())
expected={'TX1:005','TX1:027','TX1:034','TX2:046','TX1:NGB003','TX1:NGB005','TX1:NGB007','TX1:NGB008','TX2:NGB009','TX2:NGB010','TX2:NGB011','TX2:NGB012'}
open_rows={'TX1:006','TX1:031'}
standard={'propext','Classical.choice','Quot.sound'}
def gate(closed,delta,edges,audit,native,source):
 fs=closed['functions'];rs=[r for f in fs for r in f['rows']]
 assert len(rs)==len(set(rs))==12 and set(rs)==set(delta['new_closed_rows'])==expected
 assert closed['new_composed_functions']==len(fs)==8 and closed['new_composed_rows']==12
 assert not closed['headline_target_established']and not closed['trust_removed']
 assert {r['row']for r in delta['pending']}==open_rows and all(r['status']=='OPEN'for r in delta['pending'])
 assert delta['validator_checks_added_only']and delta['no_other_status_change']and delta['no_authoritative_graph_or_membership_edit']
 assert delta['Q_after_additive_delta']=={'total':161,'CLOSED':159,'OPEN':2,'QUALIFIED':0}
 assert delta['global_after_additive_delta']=={'total':599,'CLOSED':315,'OPEN':284,'QUALIFIED':0}
 assert len(edges['edges'])==15 and edges['new_closed_edges']==10 and edges['typed_alternatives_excluded']==5
 assert sum(e['status']=='EXCLUDED-TYPED-ALTERNATIVE'for e in edges['edges'])==5
 spec=next(e for e in edges['edges']if e['caller'].endswith('::CM31::inv'))
 assert spec['no_generic_function_pointer_credit']and 'fixed'in spec['scope']
 assert audit['status']=='PASS'and audit['raw_authoritative']and not audit['cold_release_replay']
 roots=J(E/'NHH_L049/sources/NHH_AUDIT_ROOTS.json')['roots'];assert len(audit['results'])==len(roots)==113
 assert {r['root']for r in audit['results']}==set(roots)and'AspisR1.RPx_Deployed.deployed'in roots
 assert all(r['equal']and set(r['walked_axioms'])<=standard for r in audit['results'])
 fixtures=audit['fixtures'];assert len(fixtures)==8 and all(r['equal']for r in fixtures)
 assert all(len(r['walked_axioms'])==1 for r in fixtures[:4])and all(not r['walked_axioms']for r in fixtures[4:])
 assert audit['scan']['modules']==13452 and audit['scan']['dangling']==audit['scan']['incompatible_owners']==audit['scan']['import_mismatches']==0
 assert native['status']=='PASS'and len(native['pairs'])==17 and native['no_field_multiplication_verified']and not native['writable_static']and not native['generic_function_pointer_credit']and native['contract_or_stub_verified_uses']==0
 assert all(p['frozen_files']==735 and p['source_matched']and p['frozen_graph']and p['unchanged_lock']and p['deployed_features']and not p['quarantined']and not p['suspended']for p in native['pairs'])
 for name in ['cm_inverse_log','qm_try_log','qm_inv_log']:assert next(p for p in native['pairs']if p['harness']==name)['control']=='canonical recorded argument corruption'
 assert next(p for p in native['pairs']if p['harness']=='qm_neg')['credit'].startswith('LOCAL ONLY')
 assert source['status']=='PASS'and len(source['targets'])==14 and not source['shipped_changes']and source['patches']['status']=='PASS'
 return True
if __name__=='__main__':
 runpy.run_path(str(E/'NHH_certify_final.py'))
 vals=[J(E/n)for n in ['NHH_CLOSED.json','NHH_LEDGER_DELTA.json','NHH_EDGES.json','NHH_AUDIT.json','NHH_NATIVE_VALIDATION.json','NHH_SOURCE_VALIDATION.json']];assert gate(*vals)
 tests=[]
 mutations=[('generic promotion',0,lambda x:x['functions'][0]['rows'].append('TX1:006')),('negation promotion',1,lambda x:x['new_closed_rows'].append('TX1:031')),('wrong Q count',1,lambda x:x['Q_after_additive_delta'].update(CLOSED=161)),('weakened validator',1,lambda x:x.update(validator_checks_added_only=False)),('false security conclusion',0,lambda x:x.update(headline_target_established=True)),('missing typed exclusion',2,lambda x:x['edges'].pop()),('generic native credit',2,lambda x:next(e for e in x['edges']if e['caller'].endswith('::CM31::inv')).update(no_generic_function_pointer_credit=False)),('nonstandard axiom',3,lambda x:x['results'][0]['walked_axioms'].append('sorryAx')),('missing raw root',3,lambda x:x['results'].pop()),('raw summary disagreement',3,lambda x:x['results'][0].update(equal=False)),('missing fixture',3,lambda x:x['fixtures'].pop()),('dangling reference',3,lambda x:x['scan'].update(dangling=1)),('incompatible owner',3,lambda x:x['scan'].update(incompatible_owners=1)),('wrong imports',3,lambda x:x['scan'].update(import_mismatches=1)),('native field multiplication claim',4,lambda x:x.update(no_field_multiplication_verified=False)),('writable static',4,lambda x:x.update(writable_static=True)),('generic pointer credit',4,lambda x:x.update(generic_function_pointer_credit=True)),('missing frozen source gate',4,lambda x:x['pairs'][0].update(frozen_files=734)),('lock drift',4,lambda x:x['pairs'][0].update(unchanged_lock=False)),('feature drift',4,lambda x:x['pairs'][0].update(deployed_features=False)),('source mismatch',4,lambda x:x['pairs'][0].update(source_matched=False)),('unmatched argument control',4,lambda x:next(p for p in x['pairs']if p['harness']=='qm_try_log').update(control='assertion inversion')),('local negation promoted',4,lambda x:next(p for p in x['pairs']if p['harness']=='qm_neg').update(credit='CLOSED')),('shipped source change',5,lambda x:x['shipped_changes'].append('field.rs'))]
 for label,i,change in mutations:
  bad=copy.deepcopy(vals);change(bad[i])
  try:gate(*bad)
  except AssertionError:tests.append(label)
  else:raise AssertionError('Accepted mutation '+label)
 # Independent source/pin checks, including exact pre-runtime scanner and raw action.
 original=(R/'evidence/slice-d-field3-20261105/NGH_Driver.lean').read_text();driver=(E/'NHH_Driver.lean').read_text();marker='/-- Standalone runtime avoids';action='  let action : CommandElabM Bool := do'
 assert original.split(marker)[0]==driver.split(marker)[0]
 assert original[original.index(action):]==driver[driver.index(action):]
 walker=(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes();assert hashlib.sha256(walker).hexdigest()==J(E/'NHH_WALKER_PIN.json')['sha256']
 finalmodules=['Embedding','BaseOps','ScalarDomain','EncodedScalar','CMInverse','CMTrace','CMSampler','CMAlgebra','CMBridge','AllScalar','CMAll','QInverse','QAll','QTrace','QBridge','QNeg','StubDomains','InverseOutcomes']
 forbidden=re.compile(r'\b(?:sorry|admit|axiom|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)')
 for m in finalmodules:
  s=(E/('NHH_'+m+'.lean')).read_text();assert not forbidden.search(s),m
  names=re.findall(r'^theorem (\w+)',s,re.M);assert all('#print axioms '+n in s for n in names)
 assert sum(len(re.findall(r'^theorem (\w+)',(E/('NHH_'+m+'.lean')).read_text(),re.M))for m in finalmodules)==112
 for p in E.rglob('*'):
  assert p.name!='__pycache__'
  if p.is_file():assert p.stat().st_size<=20_000_000,p
 result=dict(status='PASS',mutations_rejected=tests,unchanged_NGZ_gate=True,checks_removed=0,new_closed_rows=12,new_closed_edges=10,typed_exclusions=5,roots=113,proof_sources=18,explicit_top_theorems=112,scanner_prefix_byte_identical=True,raw_action_byte_identical=True,walker_byte_identical=True,source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',deployed_target_established=False)
 (E/'NHH_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(dict(status='PASS',mutations=len(tests),rows=12,roots=113)))
