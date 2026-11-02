"""Local, hash-pinned own-1 entry-to-entropy call-chain inspection."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
adopted=json.loads((E/'adopted-backend-confirmation.json').read_text())
revision=adopted['adopted_build_receipt']['revision']
def read(rev,path):return subprocess.check_output(['git','show',rev+':'+path])
def rust_body(s,anchor):
 a=s.index(anchor);i=s.index('{',a);j=i+1;n=1
 while n:
  n+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[a:j]
source=[]
for path,anchor in [
 ('crates/aspis-r1-cost-probe/src/RealR1_client.rs','pub fn prove_for_proof_accounts('),
 ('crates/aspis-r1-cost-probe/src/prover.rs','fn retry_attempt('),
 ('crates/aspis-r1-cost-probe/src/prover.rs','pub fn prove_masked_retrying_with('),
 ('crates/aspis-prover/src/state_only_entropy.rs','pub fn generate_for_mask_nonce(')]:
 raw=read('HEAD',path);old=read(revision,path)
 body=rust_body(raw.decode(),anchor)
 old_body=rust_body(old.decode(),anchor)
 assert body==old_body,('adopted selected body differs',path,anchor)
 source.append(dict(path=path,anchor=anchor,adopted_revision=revision,file_sha256=sha(raw),adopted_file_sha256=sha(old),whole_file_identical=raw==old,body_sha256=sha(body.encode()),body=body))
entry=source[0]['body']
assert 'prover::prove_masked_retrying_with' in entry
assert 'StateOnlyAttemptSecrets::generate_for_mask_nonce(proof_account(k)).map_err(|_| Error::Entropy)' in entry
funs_path='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
raw=read('HEAD',funs_path);s=raw.decode()
names=[
 'RealR1_client.prove_for_proof_accounts',
 'prover.prove_masked_retrying_with','prover.retry_attempt',
 'RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut',
 'aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce',
 'aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body']
emitted=[]
for name in names:
 m=re.search(r'\bdef\s+'+re.escape(name)+r'\s',s);assert m,name
 end=s.find('/--',m.end());body=s[m.start():end if end>=0 else len(s)]
 emitted.append(dict(name=name,body=body,sha256=sha(body.encode())))
assert 'prover.prove_masked_retrying_with' in emitted[0]['body']
assert 'prover.retry_attempt' in emitted[1]['body']
retry=emitted[2]['body']
for t in ['let (r, next_attempt1)', '.call_mut','next_attempt k','nonce_store1 next_attempt1 i']:assert t in retry,t
callback=emitted[3]['body']
for t in ['let (a, t)', 'StateOnlyAttemptSecrets.generate_for_mask_nonce\n      a','let back := fun c1 => c1','ok (r1, t, back)']:assert t in callback,t
assert 'StateOnlyAttemptSecrets.generate_for_mask_nonce_loop\n' in emitted[4]['body']
assert 'getrandom.fill' in emitted[5]['body']
prep=json.loads((E/'prepare-PV_EVH_NativeEntropyLayout.json').read_text())['result']
module=next(x for x in prep['project_checks'] if x['module']=='R1Z.ProverRwFullFuns')
assert module['source']['source_sha256']==sha(raw)
graph_path='evidence/pv-c474b-20261029/client-unit-graph.json'
graph_raw=read(revision,graph_path);graph=json.loads(graph_raw)
units=[dict(pkg_id=u['pkg_id'],features=u['features'],profile=u['profile'],mode=u['mode']) for u in graph['units']
 if u['target']['name'] in ['aspis_r1_cost_probe','aspis_prover'] and u['mode']=='build']
assert units,'adopted project feature units missing'
out=dict(evidence_class='own-1 structural actual extracted proof-account entry-to-entropy call chain; not full entry/runtime adequacy',
 source=source,nonbody_diff=subprocess.check_output(['git','diff','--unified=2',revision,'HEAD','--','crates/aspis-r1-cost-probe/src/prover.rs'],text=True),
 source_scope='Selected call-chain function bodies are byte-identical. The whole prover.rs differs by four insecure-spend-fixture cfg removals outside these bodies; no whole-file identity or full-entry adequacy is claimed.',
 emitted=emitted,emission=dict(path=funs_path,sha256=sha(raw),authority=module),
 deployed=dict(binary_sha256=adopted['adopted_build_receipt']['receipt']['sha256'],unit_graph=dict(revision=revision,path=graph_path,sha256=sha(graph_raw)),units=units),
 established=[
  'Existing RealR1_client.prove_for_proof_accounts supplies the actual entropy callback to prove_masked_retrying_with, which selects retry_attempt on S2.',
  'The emitted retry invokes next_attempt with k and recurses with next_attempt1 and nonce_store1. The callback invokes the actual proof_account(k), passes that mask to generate_for_mask_nonce, maps its source error to Error.Entropy, and returns updated capture t plus its identity backward continuation.',
  'generate_for_mask_nonce checks the public mask then reaches the original loop body and getrandom.fill; frame/layout binding applies at that reached source call, not to an unrelated entropy model.'
 ],
 retained=[
  'Actual advancing residual/native family and proof-account callback WORLD association, mutable source failure prefixes, allocator and nonce-store adequacy; no actual successful run supplied.',
  'FRAME-CALL V370, FRAME-ENTRY runtime call/stack/heap validity, HEAP-ENTRY rdea-1, KERNEL-WRITE and RAW-ABI runtime/compiler obligations in frame-source-binding-D572.json.',
  'This is the existing prover extraction, not the client main extraction or a substitute client; D520/U/D524 and all client inputs remain.'
 ],rows_removed=[],trust_fields_added=[],native_runs=0,kani_runs=0)
p=E/'entry-frame-binding-D572.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS adopted source and pinned extracted entry call chain; full native family/entry remains open')
