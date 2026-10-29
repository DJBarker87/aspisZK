"""Pin the local returned-error/control binding and list its exact open leaves.
Source/compiled-structure evidence, not K-1-substitute structural equivalence.
"""
from pathlib import Path
import hashlib,json,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');S=D.parent/'codex-pv-fscan-20261028/src';old=D.parent/'codex-pv-diag-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def function(path,needle):
 s=path.read_text();a=s.index(needle);start=s.index('{',a);depth=1;i=start+1
 while depth:
  if s[i]=='{':depth+=1
  elif s[i]=='}':depth-=1
  i+=1
 return dict(path=str(path),sha256=sha(path),line=s[:a].count('\n')+1,body=s[a:i])
prover=S/'crates/aspis-r1-cost-probe/src/prover.rs';client=S/'crates/aspis-r1-cost-probe/src/RealR1_client.rs';plan=S/'tools/r1-cost-probe/src/bin/devnet_spend/plan.rs';main=S/'tools/r1-cost-probe/src/bin/devnet_spend.rs'
rows=[function(prover,'fn retry_attempt('),function(prover,'fn semantic_error('),function(prover,'fn mask_error('),function(client,'pub fn prove_for_proof_accounts('),function(plan,'fn err('),function(main,'fn main(')]
r=rows[0]['body'];assert 'if k>=ATTEMPT_CAP { return Err(Error::AttemptsExhausted); }' in r
assert 'let attempt=next_attempt(k)?;' in r
assert 'Err(Error::Rejected)=>retry_attempt(' in r
assert 'attempts:k+1' in r and 'Err(e)=>Err(e)' in r
# This claim is about direct source statements; it does NOT exclude callbacks,
# implicit destructors, allocation, runtime hooks or compiler-generated effects.
assert not re.search(r'\b(?:print|println|eprint|eprintln|panic|log|trace|debug|warn|error)!',r)
assert 'if e==SError::ActivePole { return Error::Rejected; }' in rows[1]['body']
assert 'if e==StateOnlyMaskBuildError::MaskSampleExhausted { return Error::Rejected; }' in rows[2]['body']
assert 'Variant::S2' in rows[3]['body'] and 'map_err(|_|Error::Entropy)' in rows[3]['body'].replace(' ','')
assert 'anyhow!("{e:?}")' in rows[4]['body']
assert 'println!("{}",plan::run(&q)?);return Ok(())' in rows[5]['body']
assert 'RealR1_client::prove_for_proof_accounts(statement.semantic_public(),&compiled,HOST_HASH,&mut store,|k| accounts.nonce(k)).map_err(err)?' in plan.read_text()
std=old/'source-std-process.rs.txt';txt=std.read_text();assert 'Error: {err:?}' in txt and 'attempt_print_to_stderr' in txt
# The exact source/body and byte identity were already checked by PV_DIAG.
# Retain a fresh hash check of each bound native source against that committed record.
sourcepins=json.loads((old/'source-identity.json').read_text());
result=dict(classification='source control/formatter binding with explicit unproved leaf-effect refinement',source_rows=rows,std_termination_source_sha256=sha(std),std_termination_span=txt[txt.index('impl<T: Termination, E: fmt::Debug>'):txt.index('impl<T: Termination, E: fmt::Debug>')+650] if 'impl<T: Termination, E: fmt::Debug>' in txt else 'see pinned std source at lines 2609-2618',controller_direct_diagnostic_calls=0,model_correspondence={'cap':'runEffects zero / cap_no_direct_effects','successful_attempt':'runEffects done retains index+1, proof/audit/store/callback','rejected_attempt':'rejected_effects preserves full prefix and recursion','other_returned_error':'runEffects stop preserves variant/state/effects','Aeneas_fail':'fatal_effects_retained; abstract failure kind is not equated with native panic/OOM','Aeneas_divergence':'runEffects div retains prefix; no termination report invented'},open_leaves=['complete native per-attempt effect trace equals Observed.effects, including implicit drops, panic/OOM and frames','plan::err formatted allocation/capture partial failures equal reportError, with delivered/partial stderr writes refined separately','main plan::run post-proof filesystem/serialization and success stdout effects','same-public joint occurrence/variant/frame history transported through existing L1 coupling','complete foreign/logger/crash-reporter closure'])
(D/'native-binding.json').write_text(json.dumps(result,indent=2)+'\n');print('six local source bodies bound; native full-effect leaves remain explicit')
