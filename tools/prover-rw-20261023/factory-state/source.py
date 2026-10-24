"""Prospective native source association; no semantic proof or production edit."""
from pathlib import Path
import hashlib, json, sys
D = Path(__file__).resolve().parent
R = D.parents[2]
sha = lambda b: hashlib.sha256(b).hexdigest()
original = (D.parent/'factory-iteration/production-source.txt').read_bytes()
assert (R/'crates/aspis-prover/src/state_only_entropy.rs').read_bytes() == original
assert sha(original) == '1d48a26ba021dae55242f005bf45f4cea311d89fa32bbb064975991b6efbd57d'
old = original.decode()
start = old.index('    pub fn generate_for_mask_nonce(')
end = old.index('\n    pub fn mask_nonce(', start)
before = old[start:end]
controller = (D/'controller.rs.txt').read_text()
items = (D/'items.rs.txt').read_text()
prefix = (D.parent/'factory-iteration/proof-cut/selected.rs').read_text().split('impl StateOnlyAttemptSecrets {')[0]
selected = prefix + items + '\nimpl StateOnlyAttemptSecrets {\n' + controller + '}\n'
proposal = old[:start] + controller + old[end:] + '\n' + items
outputs = {D/'preflight/lib.rs': selected.encode(), D/'proposed-state-only-entropy.rs.txt': proposal.encode()}
meta = dict(schema='ProverRwFactoryState-prospective-v1', production_edited=False,
            original_sha256=sha(original), original_span=dict(start=start,end=end,sha256=sha(before.encode())),
            controller_before=before,controller_after=controller,new_items=items,
            selected_sha256=sha(selected.encode()),prospective_sha256=sha(proposal.encode()),
            target='ProverRwFactoryStateDraw::resume',
            statement_before='(nonce32) -> Result<Secrets,Error>',
            statement_after_public='(nonce32) -> Result<Secrets,Error>',
            statement_after_selected='Draw { Request { nonce32,retry }, Zeroizing64, Result<(),getrandom::Error> } -> (Control, Result<Option<Secrets>,Error>)',
            claim='text/source association only; native effect/P6/finite16/cleanup relations unproved')
outputs[D/'source-map.json'] = (json.dumps(meta,indent=2)+'\n').encode()
for p,b in outputs.items():
    if '--check' in sys.argv: assert p.read_bytes() == b,p
    else: p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
print('PASS prospective request/resume source association; production unchanged')
