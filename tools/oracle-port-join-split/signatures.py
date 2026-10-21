#!/usr/bin/env python3
"""Controlled deletion audit; makes no weakening claim for C7 -> split."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
OUT = PACKET / 'evidence/join-split-draft-20261021'
SOURCE = PACKET / 'lean/OraclePortJoinSplitHeadline.lean'
text = SOURCE.read_text()


def signature(name):
    start = text.index('theorem ' + name + '\n')
    end = text.index(':=', start)
    return re.sub(r'^theorem \S+', 'theorem final_soundness', text[start:end]).rstrip() + '\n'


before = signature('final_soundness_with_execution')
after = signature('final_soundness')
premise = '    (h_Rust_equals_dV : ExecutionJoin D rust)\n'
assert before.count(premise) == 1
assert before.replace(premise, '') == after
(OUT / 'split-before.lean.txt').write_text(before)
(OUT / 'split-after.lean.txt').write_text(after)
(OUT / 'deleted-premise-verbatim.lean.txt').write_text(premise)
(OUT / 'delete-redundant-execution.diff').write_text(''.join(difflib.unified_diff(
    before.splitlines(True), after.splitlines(True), fromfile='split-before', tofile='split-after')))
unchanged = []
for module in ['R1FinalSoundnessBinPerQueryR19', 'OraclePortHeadlineDVC7', 'OraclePortRuntimeBindingC7']:
    source = PACKET / 'lean' / (module + '.lean')
    rel = str(source.relative_to(ROOT))
    base = subprocess.check_output(['git', 'show', '3a01b2d6d:' + rel])
    assert base == source.read_bytes()
    unchanged.append({'path': rel, 'base': '3a01b2d6d',
                      'sha256': hashlib.sha256(base).hexdigest(), 'byte_identical': True})
(OUT / 'signature-status.json').write_text(json.dumps({
    'scope': 'Delete only the redundant execution premise after all split premises are already present. '
             'This is not an unconditional deletion or weakening of C7; frozen joins remain open.',
    'deleted_premise_verbatim': premise, 'unchanged_endpoints': unchanged,
    'original_stored_binding_retained': '(h_stored_runtime : StoredCarrierBinding D rust P runtime)'
}, indent=2) + '\n')
print('Controlled split signature deletion verified; original endpoints byte-identical')
