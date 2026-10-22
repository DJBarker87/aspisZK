#!/usr/bin/env python3
"""Read-only source/receipt checks; writes only this packet's audit receipt."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT/'docs/research/100bit-spend-path-20261013'
EVIDENCE = PACKET/'evidence/ckpt-bytes4-20261022'
LEAN = PACKET/'lean'
BASE = '531175a51'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

manifest = json.loads((EVIDENCE/'manifest.json').read_text())
current = {a['module']:a for a in manifest['attempts'] if a['final_current']}
modules = sorted(LEAN.glob('CheckpointBytes4*.lean'))
assert set(current) == {p.stem for p in modules}
theorems = 0
for p in modules:
    receipt = current[p.stem]
    assert receipt['exit'] == 0 and receipt['source_unchanged'] and receipt['axioms_accepted']
    assert receipt['source_sha256'] == sha(p)
    assert receipt['swaps'] == 0
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\b|set_option\s+(?:maxHeartbeats|maxRecDepth)', p.read_text(), re.M)
    declared = len(re.findall(r'^(?:private )?theorem ',p.read_text(),re.M))
    assert len(receipt['axioms']) >= declared
    theorems += declared
    for dep in receipt['owned_transitive_dependencies']:
        assert sha(ROOT/dep['source']) == dep['source_sha256'], dep['module']
    for key in ['argv','source_revision','wall_seconds','peak_rss_bytes','swaps','axioms','deps_fingerprint']:
        assert key in receipt
freeze = current['CheckpointBytes4Freeze']
assert len(freeze['axioms']) == 36
changed = subprocess.check_output(['git','diff','--name-only',BASE],cwd=ROOT,text=True).splitlines()
assert not any(p.startswith(('crates/','programs/')) or '/lean-candidates/' in p for p in changed)
assert not any(p.endswith('.lean') and '/CheckpointBytes4' not in p for p in changed)
assert all(p.stat().st_size <= 5_000_000 for p in EVIDENCE.rglob('*.json'))
reuse = json.loads((EVIDENCE/'reuse.json').read_text())
assert reuse['exit'] == 0 and not reuse['gates_reexecuted'] and not reuse['lean_axiom_adoption']
old = EVIDENCE.parent/'ckpt-bytes3-20261022/audit-result.json'
assert sha(old) == reuse['previous_audit_result_sha256']
verifier = ROOT/'crates/aspis-r1-cost-probe/src/verifier.rs'
assert sha(verifier) == reuse['source_verifier_sha256']
result = {
    'schema':'ckpt-bytes4-focused-audit-v1',
    'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    'modules':len(modules), 'new_theorems':theorems,
    'freeze_axiom_reports':len(freeze['axioms']),
    'current_peak_rss_bytes':max(a['peak_rss_bytes'] for a in current.values()),
    'current_swaps':sum(a['swaps'] for a in current.values()),
    'concrete_callback_content_instance_closed':True,
    'flat_semantic_weight_kernel_refinement_closed':True,
    'successful_saved_fields_closed':True,
    'source_stage_ordered_observation_join_closed':False,
    'frozen_rust_source_program_interpretation_closed':False,
    'elf_rebuild_trigger':False,
    'coherent_release_replay':False,
    'native_evidence_reused':reuse,
    'freeze_receipt':str((EVIDENCE/'CheckpointBytes4Freeze-1/receipt.json').relative_to(ROOT)),
    'next_consumer':'Source writer/resume ordered Digest32-effect reification; then reached_stage/strictStage, decision_observation/dV_frozen2 with S2/S10 and S1/S7/S8 provenance only.'
}
(EVIDENCE/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
