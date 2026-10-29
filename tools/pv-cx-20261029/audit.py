"""Pin the frozen entry sources and exact draft replacement spans without checkout edits."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-cx-20261029';rev='27b582ca44a9ef7c1fc341fb9bc58610d28ed7f1';draft='0046a7446d5519d1feb51ac502e2f7962038fac1'
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
sha=lambda b:hashlib.sha256(b).hexdigest()
paths=['tools/r1-cost-probe/src/bin/devnet_spend.rs','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs','tools/r1-cost-probe/Cargo.toml','tools/r1-cost-probe/Cargo.lock','tools/r1-cost-probe/rust-toolchain.toml','crates/aspis-r1-cost-probe/src/RealR1_client.rs']
rows=[]
for p in paths:
 b=git('show',rev+':'+p);rows.append(dict(path=p,blob=git('rev-parse',rev+':'+p).decode().strip(),sha256=sha(b),bytes=len(b)))
(E/'frozen-source-pins.json').write_text(json.dumps(dict(revision=rev,files=rows),indent=2)+'\n')
diff=git('diff','--no-ext-diff','--unified=0',draft+'^',draft,'--','tools/r1-cost-probe').decode();spans=[];p=None
for l in diff.splitlines():
 if l.startswith('+++ b/'):p=l[6:]
 m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(.*)',l)
 if m:
  a,n,b,k,context=m.groups();spans.append(dict(path=p,old_start=int(a),old_count=int(n or 1),new_start=int(b),new_count=int(k or 1),context=context.strip()))
parent=git('rev-parse',draft+'^').decode().strip()
identity=[]
for p in paths[:3]+paths[3:4]:
 old=git('show',parent+':'+p);base=git('show',rev+':'+p);identity.append(dict(path=p,draft_parent_sha256=sha(old),baseline_sha256=sha(base),identical=old==base))
(E/'D474-spans.json').write_text(json.dumps(dict(draft_revision=draft,draft_parent=parent,baseline=rev,adoption='Owner-approved direction; draft is not adopted into this baseline',identity=identity,spans=spans,bundle_remaining=['insecure-spend-fixture off','constant-time private-input decoding','N7 raw-keypair custody; final source spans not present in the identified diagnostics draft'],warning='Recompute span mapping against final owner-approved bundle; these are exact old/new draft hunks only'),indent=2)+'\n')
lean='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'
s=git('show',rev+':'+lean).decode();i=s.index('def RealR1_client.prove_for_proof_accounts');j=s.index(' :=',i)
(E/'existing-prover-signature.txt').write_text(s[i:j]+'\n')
(E/'prover-link-status.json').write_text(json.dumps(dict(rust_path='aspis_r1_cost_probe::RealR1_client::prove_for_proof_accounts',rust_callsite='tools/r1-cost-probe/src/bin/devnet_spend/plan.rs:116',existing_lean='ProverRwFull.RealR1_client.prove_for_proof_accounts',existing_signature='existing-prover-signature.txt',existing_lean_sha256=sha(s.encode()),status='NOT LINKED: requires successful executable emission and carrier/trait identity check; name alone is insufficient',duplication=False),indent=2)+'\n')
print('source pins, exact draft spans, and existing prover signature recorded')
