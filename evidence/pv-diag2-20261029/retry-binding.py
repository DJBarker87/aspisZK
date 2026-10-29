from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');old=json.loads((D/'native-binding.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for r in old['source_rows']:
 p=Path(r['path']);assert sha(p)==r['sha256'] and r['body'] in p.read_text()
controller=old['source_rows'][0];callback=old['source_rows'][3]
assert 'map_err(|_| Error::Entropy)' in callback['body']
steps=[
 ['k>=ATTEMPT_CAP','runEffects/run fuel=0','Err AttemptsExhausted, unchanged store; drop callback on return'],
 ['next_attempt(k)?','ProverRwRetryModel.attempt entropy branch','callback state retained; entropy Err aborts immediately, even if hypothetical callback returned Rejected'],
 ['generate_for_mask_nonce(proof_account(k)).map_err(|_| Error::Entropy)','clientEntropyStep/clientEntropy','proof-account callback first, then generator; any generator Err becomes Entropy; neither stage is declared silent'],
 ['prove_masked_attempt(...,attempt,nonce_store)','attempt body branch','all leaf Results and effects remain inputs; moved attempt cleanup belongs to body'],
 ['Ok((proof,audit))','done Published(proof,audit,k+1)','count and state preserved; no published projection used'],
 ['Err(Error::Rejected)','retry; runEffects append/recurse','all rejection prefix effects retained; closure moved into recursive call; no direct formatter call'],
 ['Err(e)','stop e','other variant, state and errors retained; callback drop retained as native leaf'],
 ['recursive Err AttemptsExhausted','cap_requested_text / last_rejection_reports','normal returned content fixed; no honest exhaustion exclusion or joint-law claim'],
 ['returned Rejected to plan::err','source_client_no_rejected / client_observed_api_not_rejected / rejected_not_in_report_suffix','NOT REACHED on concrete mapped-client normal-return path, for all inputs; proving panic/oom/drops remain distinct sinks'],
]
result=dict(classification='structural source-controller binding (K-1 substitute scope); complete-Result law plus finite controller validation, production callee effects not discharged',source_rows=[controller,callback,old['source_rows'][4]],steps=steps,source_laws=['ProverRwRetryModel.retry','source_client_no_rejected','client_observed_api_not_rejected','retry_sink_exact'],finite_validation=dict(path='retry-control-validation.json',sha256=sha(D/'retry-control-validation.json')),source_models={str(p.name):sha(p) for p in (D/'sources').glob('PV_DIAG2_*.lean')},compiler_boundary='V370 / owner pending D381/D386; no machine-code equality silently assumed',open=['all native leaf/drop/unwind execution effects','L1 V347-V351 joint occurrence/variant/history law including ActivePole','entropy failure witness independence under option B','all post-prover plan/main errors and captures'])
(D/'retry-structural-binding.json').write_text(json.dumps(result,indent=2)+'\n');print('bound exact retry/callback source; final-Rejected normal-return exclusion; other sinks explicit')
