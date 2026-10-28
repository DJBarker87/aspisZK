"""Read-only declaration/source diagnostics, never extraction authority."""
from pathlib import Path
import hashlib, json, re, subprocess

R = Path(__file__).resolve().parents[2]
E = R / 'evidence/pv-runjoin37-20261028'
E.mkdir(exist_ok=True)
def git(*args):
    return subprocess.check_output(['git', *args], cwd=R)
def pin(path):
    b = (R / path).read_bytes()
    assert b == git('show', 'HEAD:' + path)
    return dict(path=path, blob=git('rev-parse', 'HEAD:' + path).decode().strip(),
                sha256=hashlib.sha256(b).hexdigest())

old = json.loads((R / 'evidence/pv-runjoin34-20261028/oracle-source-ambiguities.json').read_text())
variants = []
for v in old['unresolved'][0]['variants']:
    p = v['path']; s = (R / p).read_text()
    record = pin(p)
    assert record['sha256'] == v['sha256']
    declarations = []
    for m in re.finditer(r'(?m)^(?:private\s+)?def\s+([^\s(]+)', s):
        preceding = s[:m.start()]
        doc = preceding[preceding.rfind('/--'):]
        declarations.append(dict(name=m[1], line=s.count('\n', 0, m.start()) + 1,
                                 source_comment=doc.strip()))
    names = [d['name'] for d in declarations]
    record.update(declarations=declarations,
        has_terminal_parts='pool_v1.pair_forest_semantic_terminal.terminal_parts' in names,
        has_op227_body='pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31' in names,
        mentions_selected_mask_value='state_only_selected_mask_value' in s,
        has_op117_body='state_only_hiding.state_only_selected_mask_value' in names)
    variants.append(record)

assert len(variants) == 6
assert all(v['has_op227_body'] and not v['has_op117_body'] for v in variants[2:])
assert all(not v['mentions_selected_mask_value'] for v in variants[2:])
base = 'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'
ep = base + 'ProverRwFullExternalFuns.lean'
external = (R / ep).read_text()
assert 'r0.Public.terminal_qm31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op227' in external
assert 'state_only_hiding.state_only_selected_mask_value [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op117' in external
paths = [ep, base + 'ProverRwFullFuns.lean',
    'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs',
    'crates/aspis-core/src/state_only_hiding.rs',
    'crates/aspis-r1-cost-probe/src/host_semantic.rs',
    'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitOracle55.lean',
    'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTerminalZero55.lean',
    'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitTerminalQName55.lean',
    'evidence/pv-batch3-20261027/lean/PV_B3_Install117.lean',
    'evidence/pv-batch3-20261027/lean/PV_B3_AuditSourceD324.lean']
candidate = git('rev-parse', 'codex/cx-prover-rw-20261023').decode().strip()
b3diff = git('diff', 'HEAD..' + candidate, '--', 'evidence/pv-batch3-20261027')
assert not b3diff
matches = git('grep', '-n', 'op227 :=', candidate, '--', '*.lean', '*.lean.txt').decode()
(E / 'candidate-op227-assignments.txt').write_text(matches)
shipped = git('diff', '82566acdfb..HEAD', '--', 'crates/', 'programs/', 'tools/r1-cost-probe')
assert not shipped
out = dict(source_revision=git('rev-parse', 'HEAD').decode().strip(),
    candidate_revision=candidate, evidence_class='read-only source/declaration identification; no source law or native fidelity claimed',
    variants=variants, input_pins=[pin(p) for p in paths],
    mask_only_diagnostic=pin('evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean'),
    relevant_callback=dict(op=227, row='V244',
        symbol='aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public::terminal_qm31',
        source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', line=2080),
    distinct_closed_callback=dict(op=117, row='V217',
        symbol='aspis_core::state_only_hiding::state_only_selected_mask_value',
        source='crates/aspis-core/src/state_only_hiding.rs', line=647),
    candidate_batch3_diff_empty=True, merge_needed_for_batch3=False,
    stage_A_shipped_subtree_diff_empty=True,
    promoted_variant=None, imported_historical_cone=False,
    extractor_launched=False, lean_starts=0, kani_starts=0)
(E / 'source-mapping.json').write_text(json.dumps(out, indent=2) + '\n')
print('Mapped all six variants: four terminal/op227 variants; no op117 body in those four.')
print('Batch-3 source diff empty; frozen shipped subtree diff empty.')
