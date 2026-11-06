from pathlib import Path
import json,hashlib
B=Path.cwd();x=json.loads((B/'PCE_NATIVE_INPUTS.json').read_text());records=x['records']
required=['pair-forest-account-evidence','pair-forest-source-invariant-audit','pair-forest-source-result-invariant-audit','pair-forest-verifier-lane-invariant-audit','r1-split-checkpoint']
for a,r in records.items():
 assert r['graph']['graph_matches_frozen'],a
 assert r['lock']['unchanged'] and r['lock']['before']==r['lock']['after']==r['graph']['lock_sha256'],a
 assert r['config']['env']['CARGO_NET_OFFLINE']=='true',a
 assert '--locked' not in r['config']['native_command'],a
 command=r['config']['native_command'];manifest=command[command.index('--manifest-path')+1]
 if '/programs/aspis-pool/' in manifest:assert all(v in r['features'].splitlines()[0] for v in required),a
 else:assert '/crates/aspis-statement/' in manifest and 'FEATURES=pool-v1-kernel' in r['features'].splitlines()[0],a
 assert r['graph']['all_crate_features'] and r['graph']['selected_closure'],a
 assert 'VERIFICATION:- ' in r['stdout'] and 'Timed out' not in r['stdout'],a
for pos,neg in x['pairs']:
 p,n=records[pos],records[neg]
 assert 'VERIFICATION:- SUCCESSFUL' in p['stdout'],pos
 assert 'VERIFICATION:- FAILED' in n['stdout'],neg
 assert p['graph']['all_crate_features']==n['graph']['all_crate_features'],(pos,neg,'feature difference')
 assert p['graph']['selected_closure']==n['graph']['selected_closure'],(pos,neg,'closure difference')
for a in ['PCB_K074','PCB_K075']:assert 'VERIFICATION:- SUCCESSFUL' in records[a]['stdout'],a
for a in ['PCB_K076','PCB_K077','PCB_K119']:assert 'VERIFICATION:- FAILED' in records[a]['stdout'],a
result=dict(status='PASS',native_runs=0,retained_receipts=len(records),matched_pairs=len(x['pairs']),all_graphs_frozen=True,all_locks_unchanged=True,all_crate_features_recorded=True,source='PCE_NATIVE_INPUTS.json',source_sha256=hashlib.sha256((B/'PCE_NATIVE_INPUTS.json').read_bytes()).hexdigest(),note='Inherited accepted certificates re-gated by unchanged import bytes; this validates retained candidate/own-helper controls, not a new native proof.')
(B/'PCE_NATIVE_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n')
print('PCE retained native validation PASS; no native execution.')
