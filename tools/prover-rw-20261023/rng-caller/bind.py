from pathlib import Path
import hashlib,json,re,sys
D=Path(__file__).resolve().parent;R=D.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p):return dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size)
def decl(path,needle,label):
 s=(R/path).read_text();a=s.index(needle);start=s.rfind('\n',0,a)+1;b=s.index('{',a);depth=1;i=b+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 text=s[start:i]
 return dict(qualified=label,path=path,span=[s.count('\n',0,start)+1,s.count('\n',0,i)+1],file=pin(R/path),signature=text[:text.index('{')],signature_sha256=sha(text[:text.index('{')].encode()),body_sha256=sha(s[b:i].encode()),text=text)
entries=[]
for p,n,q in [
('crates/aspis-r1-cost-probe/src/RealR1_client.rs','pub fn prove_for_proof_accounts','RealR1_client::prove_for_proof_accounts'),
('crates/aspis-r1-cost-probe/src/prover.rs','pub fn prove_masked_retrying_with','prover::prove_masked_retrying_with'),
('crates/aspis-r1-cost-probe/src/prover.rs','fn retry_attempt','prover::retry_attempt'),
('crates/aspis-r1-cost-probe/src/prover.rs','fn prove_masked_attempt','prover::prove_masked_attempt'),
('crates/aspis-r1-cost-probe/src/prover.rs','fn prove_masked_with_attempt','prover::prove_masked_with_attempt'),
('crates/aspis-r1-cost-probe/src/prover.rs','fn mask_error','prover::mask_error'),
('crates/aspis-r1-cost-probe/src/verifier.rs','pub enum Error','verifier::Error'),
('crates/aspis-prover/src/state_only_entropy.rs','pub enum StateOnlyAttemptEntropyError','state_only_entropy::StateOnlyAttemptEntropyError'),
('crates/aspis-prover/src/state_only_entropy.rs','impl From<getrandom::Error>','state_only_entropy::From<getrandom::Error>'),
('crates/aspis-prover/src/state_only_entropy.rs','pub fn generate_for_mask_nonce','state_only_entropy::StateOnlyAttemptSecrets::generate_for_mask_nonce'),
('crates/aspis-prover/src/state_only_entropy.rs','pub fn reserve_and_build_pool_v1_pair_forest_mask_material_v1','state_only_entropy::StateOnlyAttemptSecrets::reserve_and_build_pool_v1_pair_forest_mask_material_v1'),
('crates/aspis-prover/src/state_only_entropy.rs','impl StateOnlyMaskNonceStore for PreReservedNonce','state_only_entropy::PreReservedNonce::reserve')]:entries.append(decl(p,n,q))
llbc=D/'ProverRwRngCaller.llbc';d=json.loads(llbc.read_text())['translated'];source=(D/'prototype/lib.rs').read_text()
assert next(f['contents'] for f in d['files'] if f['name']=={'Local':'lib.rs'})==source
emitted=[]
for group in ['fun_decls','type_decls','trait_decls','trait_impls','global_decls']:
 for x in d[group]:
  if not x:continue
  meta=x['item_meta'];text=meta.get('source_text')
  emitted.append(dict(group=group,qualified=meta['name'],span=meta['span'],local=meta['is_local'],opacity=meta['opacity'],source_sha256=sha(text.encode()) if text else None,signature_sha256=sha(json.dumps(x.get('signature',x.get('generics')),sort_keys=True).encode()),body_sha256=sha(json.dumps(x.get('body',x.get('kind')),sort_keys=True).encode())))
out=dict(schema='rng-caller-source-map-v1',base='03444c5e5e',native=entries,prototype=pin(D/'prototype/lib.rs'),llbc=pin(llbc),embedded_source_matches=True,emitted=emitted,substitutions=[
'Prior cap16 owned prototype u8 error positions become actual getrandom::Error dependency 0.3.4; Os conversion calls actual source-shaped From; byte arrays unchanged. No checked universal cap16 carrier transport is claimed.',
'Native selected closure expression proof_account(k) then generate_for_mask_nonce(...).map_err(|_|Error::Entropy) becomes split locals; owned provider and returned FnMut policy state outside Result.',
'Native public/compiled/hash parameters and actual prove_masked_attempt are cut at Body interface; generic L store and B mutable body state returned outside Result; no equation associating Body with native producer is assumed.',
'Native MaskedFixtureAudit payload becomes u64 placeholder; no native payload relation is asserted. Proof bytes remain Vec<u8>. Error variants copied in full for prover/r1p-check configuration.',
'Variant!=S2 guard becomes !is_s2; actual selected callback always selects S2; native Variant-to-bool projection is not a compiled whole-native refinement.',
'Actual retry cap8, callback failure, success count k+1, only Rejected recursion, and fatal branches copied; recursive ownership moves preserve returned provider/policy/store/body.',
'Native Zeroizing new/deref and existing cap16 value installation preserved; physical Drop/zeroization remains unproved.',
'Borrowed FnMut body return emission is ill-typed under pinned FnMut.call_mut pair signature. Owned L->(L,Result) cut is explicit replacement, not a proof of native body/reservation.',
'Native Error extraction retained transparent getrandom Error=core NonZero<I32,NonZeroI32Inner>; core types are uninstalled NativeTypes parameters due unsupported TPattern range validity. No u8 tag or native layout association.',
'Reservation/layout/atomic durable filesystem/pre-reserved acknowledgment source only pinned and printed; not extracted into proved Body. Mock ledger tests do not establish native ledger closure.'
],native_changes=False)
path=D/'source-map.json';render=json.dumps(out,indent=2)+'\n'
if '--check' in sys.argv:assert path.read_text()==render
else:path.write_text(render)
print('source-map checked',sha(render.encode()))
