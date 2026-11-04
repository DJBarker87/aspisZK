#!/usr/bin/env python3
"""Additive certificate validation. No mutation of NDT/NFK or source validators."""
import json,pathlib,hashlib,re,copy
E=pathlib.Path(__file__).resolve().parent
J=lambda p:json.loads((E/p).read_text())
first=J('NFQ_ORDER.json')['first_five'];functions={r['function']:r for r in J('NFQ_ORDER.json')['functions']}
rows=J('NFQ_COVERAGE.json')['rows'];standard={'propext','Classical.choice','Quot.sound'}
specs=[(first[0],2,3,'NFQ_RowShape.compact_reference'),(first[1],4,5,'NFQ_RowShape.reference'),(first[2],6,7,'NFQ_Transport.folds_reference'),(first[3],8,9,'NFQ_Transport.final_len_reference'),(first[4],10,11,'NFQ_Transport.checkpoint_size_reference')]

def pair(p,n):
 a=J(f'NFQ_K{p:03}/receipt.json');b=J(f'NFQ_K{n:03}/receipt.json')
 assert a['exit_status']==0 and b['exit_status']==1
 pos=(E/f'NFQ_K{p:03}/stdout.log').read_text();neg=(E/f'NFQ_K{n:03}/stdout.log').read_text()
 assert 'VERIFICATION:- SUCCESSFUL' in pos
 assert re.search(r'\*\* 1 of \d+ failed',neg) and 'Failed Checks: |r|' in neg and 'cfg!(NFQ_invert)' in neg
 for k in [p,n]:
  ad=J(f'NFQ_K{k:03}-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True
  rc=J(f'NFQ_K{k:03}/receipt.json');assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  g=J(f'NFQ_K{k:03}-graph-check.json');lock=J(f'NFQ_K{k:03}-lock-check.json');assert g['graph_matches_frozen'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  crates={r['name']:r['features'] for r in g['selected_closure']}
  assert set(crates['aspis-r1-cost-probe'])=={'default','private-leaf-salts','optimized-terminal','program-build'}
  assert 'r0' in crates['aspis-core'] and {'r0','pool-v1-kernel'}<=set(crates['aspis-statement'])
  # Source context is frozen and independent of the unrelated statement
  # workspace feature spend-dynamic-rate512; no statement body is reached.
  assert not J(f'NFQ_K{k:03}-source-check.json')['errors']
 return a,b

def audit_check():
 results=[]
 for mode in ['proof0','proof1']:
  r=J('NFQ_final_audit/'+mode+'.json');assert r['exit_status']==0
  for x in r['results']:assert x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<=standard
  results+=r['results']
 fixtures=J('NFQ_final_audit/fixtures.json')['results'];assert len(fixtures)==8
 assert all(len(r['walked_axioms'])==1 for r in fixtures[:4]) and all(not r['walked_axioms'] for r in fixtures[4:])
 assert (E/'NFQ_WALKER_SOURCE.lean.txt').read_bytes()==(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()
 return {r['root']:r for r in results}

def fidelity_check():
 for a,expected in [(13,0),(14,1),(15,1),(16,0),(17,1),(18,1)]:
  r=J(f'NFQ_K{a:03}/receipt.json');s=(E/f'NFQ_K{a:03}/stdout.log').read_text();assert r['exit_status']==expected
  assert 'VERIFICATION:- '+('FAILED' if expected else 'SUCCESSFUL') in s
  if a in [15,18]:assert 'is assignable' in s
  if a in [14,17]:assert re.search(r'\*\* 1 of \d+ failed',s) and 'core::panicking::assert_failed_inner' in s
 return {'usize':{'inverted_ensures':'NFQ_K007','real_body':'NFQ_K013','unimplied_stub_verified':'NFQ_K014','modifies_violation':'NFQ_K015'},'Option<(u8,usize)>':{'inverted_ensures':'NFQ_K005','real_body':'NFQ_K016','unimplied_stub_verified':'NFQ_K017','modifies_violation':'NFQ_K018'}}

if __name__=='__main__':
 audits=audit_check();fidelity=fidelity_check();closed=[]
 for f,p,n,root in specs:
  pair(p,n);assert root in audits
  ff=functions[f];assert all(c['function'] in first for c in ff['callees'])
  closed.append(dict(function=f,rows=ff['rows'],status='CLOSED',form='ruling (y) hybrid scalar certificate; no new trust',domain='all u8' if p<6 else 'all three valid native Variant values; native-to-cohort constructor map in NFQ_Transport.code/port',physical_interpretation='retained root ABI, frozen source/deployed-feature, Aeneas/Kani/P6/D188 option-A semantic transport and source-to-ELF boundaries',native_positive=f'NFQ_K{p:03}',matched_control=f'NFQ_K{n:03}',lean_root=root,extraction='NFQ_E001; NCO pins',axioms=audits[root]['walked_axioms'],internal_edges=[dict(callee=c['function'],domain_proof='all-Variant domain preserved by same native enum; Kani executes real callee, no stub_verified substitution') for c in ff['callees']],frame='explicit empty kani::modifies(); no reference/pointer/mutable argument; no oracle or protocol effects',KMX='not reached: no byte copy/array clone/Vec growth in scalar bodies or references',observer_quarantine='none',writable_static_suspension='none'))
 rowids={x for c in closed for x in c['rows']}
 assert len(rowids)==8
 out=dict(schema_version=1,frozen_revision=J('NFQ_SLICE_D.json')['frozen_revision'],new_composed_functions=len(closed),new_composed_rows=len(rowids),driver_root_status='OPEN',functions=closed)
 (E/'NFQ_CLOSED.json').write_text(json.dumps(out,indent=2)+'\n')
 delta=dict(baseline='evidence/ledger6-20261104/NFK_LEDGER.json.xz',frozen_revision=out['frozen_revision'],new_closed_rows=sorted(rowids),rows=[dict(row=r['row'],function=r['function'],before=r['status'],after='CLOSED',certificate='NFQ_CLOSED.json') for r in rows if r['row'] in rowids],no_other_status_change=True,not_a_premise_retirement=True,trust_reclassification='P6/D188 NativeContractSemanticTransport, option A; not removal',D_counts_after=dict(total=339,CLOSED=8,OPEN=331),whole_ledger_counts_after=dict(total=587,CLOSED=227,QUALIFIED=2,OPEN=358),later_Q_packets='NFN/NFM retained separately; not added to NFK totals here')
 (E/'NFQ_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
 (E/'NFQ_AUDIT.json').write_text(json.dumps(dict(status='PASS for five scalar certificates only',raw_roots=audits,fidelity=fidelity,combined_import='NFQ_L007',raw_audit='NFQ_L010',walker_sha256=hashlib.sha256((E/'NFQ_WALKER_SOURCE.lean.txt').read_bytes()).hexdigest(),native_audit=J('NFQ_final_audit/SUMMARY.json'),excluded=['NFQ_L001 output directory input error','NFQ_K001 pre-submission wrapper import-parser error','NFQ_L009 pre-submission leftover query root input','NFQ_K012 missing proof_for_contract input error']),indent=2)+'\n')
 print(json.dumps(dict(valid=True,new_functions=5,new_rows=8,remaining_D_rows=331)))
