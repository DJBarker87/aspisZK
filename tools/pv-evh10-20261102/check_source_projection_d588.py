"""D588 pinned source review, not a Lean proof or semantic absence claim."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

BASE = '102cacae1c'
E = Path('evidence/pv-evh10-20261102')
sha = lambda b: hashlib.sha256(b).hexdigest()
paths = [
    'lean/PV_EVH_NativeOperatorProver.lean',
    'lean/PV_EVH_AccountCallback.lean',
    'lean/PV_EVH_Entropy.lean',
    'lean/PV_EVH_NativeRawSelection.lean',
    'lean/PV_EVH_World.lean',
    'lean/PV_EVH_WorldLoop.lean',
    'lean/PV_EVH_Prefix.lean',
    'lean/PV_EVH_Runtime.lean',
    'lean/PV_EVH_NonceWorld.lean',
    'lean/PV_EVHB_ReserveWorld.lean',
    'lean/PV_EVHB_SaltsReserve.lean',
    'lean/PV_EVHB_CallbackEffects.lean',
    'lean/PV_EVHB_CallbackSelection.lean',
    'lean/PV_EVHB_PrivateSaltsNew.lean',
    'lean/PV_EVHB_WorkerRequests.lean',
    'lean/PV_EVH_LiteralDiagnostics.lean',
    'lean/PV_EVH_LiteralWriteAll.lean',
    'lean/PV_EVH_RuntimeBinding.lean',
    'lean/PV_RJ4IDB_NativeTrace.lean',
    'lean/PV_RJ4IDB_Channels.lean',
]
sources = {}
pins = []
for p in paths:
    raw = subprocess.check_output(['git', 'show', BASE + ':' + p])
    assert Path(p).read_bytes() == raw, ('source changed', p)
    sources[p] = raw.decode()
    pins.append(dict(path=p, sha256=sha(raw)))
entry = sources[paths[0]]
assert 'def entry_OPEN' in entry
for h in ['same', 'account_fixed', 'hh', 'hb', 'hr', 'hf', 'ha', 'hbuild',
          'hsaltLeaves', 'hsaltStep', 'hprepare', 'hfinish', 'hpublish',
          'hmaterial', 'frame_fixed']:
    assert re.search(r'\(' + h + r'\s*:', entry), h
assert '(same : ∀ n s, answers n s = getrandom.fill s)' in entry
assert 'answers w.entropyCursor buffer' in sources['lean/PV_EVH_Entropy.lean']
assert 'abbrev P (A : Type) := World → Prefix A' in sources['lean/PV_EVH_Prefix.lean']
world = sources['lean/PV_EVH_World.lean'].split('structure World where')[1].split('structure Run')[0]
assert not re.search(r'^  (allocator|stack|threads?)\s*:', world, re.M)
status = sources['lean/PV_EVH_WorldLoop.lean'].split('inductive Status')[1].split('structure Prefix')[0]
assert '| finished (result : Result A)' in status and '| exhausted' in status
assert '| fault' not in status
assert 'abbrev Q (A : Type) := State → Run A' in sources['lean/PV_EVH_Runtime.lean']
assert '| fault (error : Fault)' in sources['lean/PV_EVH_Runtime.lean']
assert 'caller p.1 p.2' in sources['lean/PV_EVHB_ReserveWorld.lean']
assert 'prover.derive_private_salts_loop reserved context hash tag count' in sources['lean/PV_EVHB_SaltsReserve.lean']
assert 'derive_private_salts_loop_OPEN :' in sources['lean/PV_EVHB_PrivateSaltsNew.lean']
fields = ['native', 'fileTrace', 'countTrace', 'timeTrace', 'oraclePrefix']
for field in fields:
    assert re.search(r'^  ' + field + r' := missing\.' + field + r'_OPEN$',
                     sources['lean/PV_EVH_RuntimeBinding.lean'], re.M), field
# Verify the previously committed binary evidence attachment; no physical proof work.
l3 = json.loads((E / 'l3-residual-D588.json').read_text())
assert l3['classification'] == 'V370/L3' and l3['projection_premise'] is False
for p in l3['evidence']:
    assert sha(Path(p['path']).read_bytes()) == p['sha256']
# Resolve the generated source through the SAME recorded cohort authority.
authority = json.loads(Path('evidence/pv-evh4-20261029/prepare-PV_EVH_World.json').read_text())['result']
funs = next(x for x in authority['project_checks'] if x['module'] == 'R1Z.ProverRwFullFuns')
funs = funs['source']
raw = subprocess.check_output(['git', 'show', funs['revision'] + ':' + funs['path']])
assert sha(raw) == funs['source_sha256']
assert b'def RealR1_client.prove_for_proof_accounts' in raw
result = dict(
    source_revision=subprocess.check_output(['git', 'rev-parse', BASE], text=True).strip(),
    evidence_class='pinned source inspection only; not semantic absence or a Lean theorem',
    source_pins=pins,
    documentation_pins=[dict(path=str(p), sha256=sha(p.read_bytes())) for p in
        [E / 'L3-RESIDUAL.md', E / 'BLOCKER-D588.md', Path(__file__)]],
    extraction_authority=dict(module='R1Z.ProverRwFullFuns', **{k: funs[k] for k in ['path', 'revision', 'source_sha256', 'git_blob']}),
    l3_residual='ActualEntropyEntryPrefix source-to-machine carrier',
    l3_class='V370/L3', l3_projection_premise=False,
    allowed_conditional_premises=['OWNER', 'op227', 'op257'],
    additional_hypotheses_added=[], trust_fields_added=[], rows_removed=[],
    selectors_still_OPEN=fields, source_entry_world_constructed=False,
    five_equations_proved=False,
    stop='inherited focus rule: concrete source entry world composition remains unconstructed',
    lean_attempts=0, native_attempts=0, host_scopes=0,
    new_axioms_audit=None, historical_axioms_mode='SUMMARY-BASED',
    next_lean=90267, subsequent_lean=[91500, 91596],
    subsequent_audits=[91597, 91599], next_native='N91603',
)
out = E / 'source-projection-D588.json'
if '--check' in sys.argv:
    assert json.loads(out.read_text()) == result
else:
    out.write_text(json.dumps(result, indent=2) + '\n')
print('PASS D588 source review and L3 attachment; five projections remain unconstructed')
