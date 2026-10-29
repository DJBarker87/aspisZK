"""Adopted release-erased trace member, with no observer or copy value claim."""
from pathlib import Path
import json,subprocess,hashlib,sys
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text());read=lambda p:subprocess.check_output(['git','show','HEAD:'+p],cwd=R)
B=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');assert sha((E.parent/'native-ledger3-20261029/NDT_LEDGER.json').read_bytes())==obj(E/'NEB_SCOPE.json')['ledger_sha256'];fn='crates/aspis-r1-cost-probe/src/trace.rs::value';rows=[r for r in B['rows'] if r['function']==fn];assert len(rows)==2
for r in rows:
 assert r['bridge_status']=='CLOSED-CONDITIONAL' and r['frozen_body_verified'] and not r['no_credit_reason'] and all(p['status']=='SAME BODIES' for p in r['feature_parity'])
 raw=subprocess.check_output(['git','show',B['frozen_revision']+':'+r['source_file']],cwd=R);a,b=r['frozen_body_byte_range'];body=raw[a:b];assert sha(body)==r['frozen_body_sha256'] and sha(raw)==r['source_file_sha256']
 assert b'#[cfg(not(feature="prover"))]\n    let _ = (tag,index,x);' in body
 assert b'#[cfg(feature="prover")]\n    VALUES.with' in body
 assert all(o['status']=='OPEN' for o in r['inventory_domain_obligations']) and all(o.get('call',{}).get('cfg')==['#[cfg(feature="prover")]'] and o['call']['resolution']=='disabled release cfg' for o in r['caller_domain_obligations'])
 for p,h in r['receipt_sha256'].items():assert sha(read(p))==h
claim=next(c for c in B['claims'] if c['claim_id']=='NBC::value');assert claim['admissible_local_credit'] and 'prover absent' in str(claim['source_claim_text'])
packet='evidence/native-tx2a-20261027/';d=json.loads(read(packet+'NBC_K003/receipt.json'));g=json.loads(read(packet+'NBC_K003-graph-check.json'));log=read(packet+'NBC_K003/stdout.log').decode()
assert d['exit_status']==0 and d['swaps']=='0' and d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert g['graph_matches_frozen'] and g['resolved_packages']==441 and not g['edge_errors'] and not g['new_package_tuples']
lock=sha(subprocess.check_output(['git','show',B['frozen_revision']+':Cargo.lock'],cwd=R));assert g['lock_sha256']==d['source_hashes']['NBC_src/Cargo.lock']==lock
assert 'VERIFICATION:- SUCCESSFUL' in log
deployed=obj(E/'NEB_IMPORTED_POINT/NEA_K017-graph-check.json');features=next(p['features'] for p in deployed['resolved_features_all_crates'] if p['name']=='aspis-r1-cost-probe');assert 'prover' not in features and all(f in features for f in ['default','private-leaf-salts','optimized-terminal','program-build'])
out=dict(selected_library_features=features,selected_deployed_graph_sha256=sha((E/'NEB_IMPORTED_POINT/NEA_K017-graph-check.json').read_bytes()),schema='NEB-trace-adopted-review-v1',function=fn,frozen_body_sha256=rows[0]['frozen_body_sha256'],authoritative_ledger_sha256=obj(E/'NEB_SCOPE.json')['ledger_sha256'],native_receipt_sha256=sha(read(packet+'NBC_K003/receipt.json')),native_evidence_role='Native no-op reachability/termination only, zero assertions; value/frame proof is exact erased-source shape and selected emitted noop. Never represented as a native output-equivalence assertion.',feature='prover absent; adopted NCS SAME BODIES association, not new feature replay',domain='All typed u16 tags, usize indices and arbitrary raw eight-limb carrier',copy_dependency='No argument or copied value is inspected or returned; conclusion depends only on deployed empty body. No copy correctness credit claimed.',function_pointer_dependency=False,new_native_attempts=0,trust='Existing adopted native/cohort release no-op transport; owner option A is P6/D188 RECLASSIFICATION, never removal',excluded='Observer/mark callbacks; prover instrumentation; enclosing operand evaluation and parent callsite association remain outside this local result. NBC_L001 failure excluded.')
p=E/'NEB_TRACE_REVIEW.json'
if '--check' in sys.argv:assert obj(p)==out
else:p.write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(adopted_trace_occurrences=len(rows),new_native_attempts=0)))
