#!/usr/bin/env python3
"""Read-only audit of the focused endpoint packet; does not run Lean."""
import hashlib
import json
import pathlib
import re
import shlex
import subprocess

root = pathlib.Path(__file__).resolve().parents[1]
repo = pathlib.Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
rows = [json.loads(x) for x in (root / 'r1p-final/endpoint-attempts-9600-9799.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows}) == len(rows)
assert all(9600 <= r['attempt'] <= 9799 for r in rows)
assert all(int(r['swaps']) == 0 for r in rows)
assert len({(r['module'], r['source_sha256'], r['deps_fingerprint']) for r in rows}) == len(rows)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
selected = []
for name, attempt in [('PhaseProtocolCoverageBin', 9611), ('PrivacyR1FinalProtocol', 9615), ('PhaseProtocolConsistencyBin', 9616)]:
    src = root / ('lean/R1Z/' + name + '.lean')
    source = src.read_text()
    digest = hashlib.sha256(src.read_bytes()).hexdigest()
    row = next(r for r in rows if r['attempt'] == attempt)
    assert row['module'] == 'R1Z/' + name and row['source_sha256'] == digest
    assert row['exit'] == 0 and int(row['peak_rss_kib']) < 7 * 1024 * 1024
    code = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b', code)
    names = re.findall(r'^theorem (\w+)', source, flags=re.M)
    audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", row['output'], flags=re.S)
    assert len(audits) == len(names)
    for theorem in names:
        assert '#print axioms ' + theorem in source
        match = next(a for a in audits if a[0].endswith('.' + theorem))
        used = {x.strip() for x in match[1].split(',') if x.strip()}
        assert used <= allowed, match
    selected.append(dict(module=row['module'], attempt=attempt, source_sha256=digest,
        source_revision=row['source_revision'], deps_fingerprint=row['deps_fingerprint'],
        exit=row['exit'], wall=row['wall'], peak_rss_kib=row['peak_rss_kib'], swaps=row['swaps'],
        axioms=[dict(theorem=a, axioms=[x.strip() for x in b.split(',')]) for a, b in audits]))

old = (root / 'lean/R1Z/PrivacyR1Final.lean').read_text()
new = (root / 'lean/R1Z/PrivacyR1FinalProtocol.lean').read_text()
old = old[old.index('theorem privacy_R1_final'):old.index(' := by\n  let R_rom_classical')]
new = new[new.index('theorem privacy_R1_protocol'):new.index(' := by\n  exact PrivacyR1Final')]

def binder(text, name):
    start = text.index('(' + name + ' :')
    depth = 0
    for i in range(start, len(text)):
        depth += (text[i] == '(') - (text[i] == ')')
        if depth == 0:
            return text[start:i+1]
    raise AssertionError(name)

def normalized(text):
    text = text.replace('(prover base ((base.pubBytes x).length) h B outputs x seed).toProver', 'Pr')
    text = text.replace('(wire base ((base.pubBytes x).length) h B outputs x).toWire', 'W')
    text = text.replace('(Pr)', 'Pr').replace('(W)', 'W')
    return re.sub(r'\s+', '', text)

retained = ['hB', 'hpub', 'builder_refinement_D46_D51', 'cF', 'R_commit_equal_fibres',
    'L₁ L₂', 'R_commit_exhaustion', 'R_commit_counter₁', 'R_commit_counter₂',
    'R_commit_stream₁', 'R_commit_stream₂', 'R_wire_coin_carrier', 'R_wire_D80_batches',
    'R_wire_D80_ordered_log', 'R_commit_cell_count', 'R_commit_blocks₁', 'R_commit_blocks₂',
    'source', 'observer_program', 'R_wire_builder_checker_D75_retry', 'G_sim_R_wire']
for name in retained:
    assert normalized(binder(old, name)) == normalized(binder(new, name)), name
for removed in ['D', 'ι', 'hι', 'R_wire_Sem1Uniform', 'R_wire_read_coverage', 'R_causal_D80', 'R_commit_D80']:
    assert '(' + removed + ' :' not in new, removed
assert normalized(old[old.rindex('    ZK_FSS'):]) == normalized(new[new.rindex('    ZK_FSS'):])
for line in ['[Fintype source.RealRand] [Nonempty source.RealRand]',
             '[Fintype source.IdealRand] [Nonempty source.IdealRand]']:
    assert line in old and line in new
statement = (root / 'r1p-final/PRIVACY-PROTOCOL-ENDPOINT-20261021.md').read_text()
assert new in statement

unchanged = {}
for module in ['PrivacyR1Final', 'PhaseProtocolInstanceBin', 'BuilderSource']:
    path = root / ('lean/R1Z/' + module + '.lean')
    rel = str(path.relative_to(repo))
    base = subprocess.check_output(['git', 'show', 'b9c171232:' + rel])
    assert base == path.read_bytes(), module
    unchanged[rel] = hashlib.sha256(base).hexdigest()

remote = 'dombarker@100.108.41.90'
evidence = '/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
cmd = '\n'.join('cat ' + shlex.quote(evidence + '/sha-' + str(r['attempt']) + '.txt') for r in rows)
host_pins = subprocess.check_output(['ssh', remote, cmd], text=True).splitlines()
assert len(host_pins) == len(rows)
for row, pin in zip(rows, host_pins):
    assert pin.split()[0] == row['source_sha256'], row['attempt']
objects = ['/home/dombarker/project-offloads/aspis-joint-20261019/objects/' + r['module'] + '.olean' for r in selected]
object_rows = subprocess.check_output(['ssh', remote,
    'sha256sum ' + ' '.join(shlex.quote(x) for x in objects) + '\nstat -c "%s %n" ' +
    ' '.join(shlex.quote(x) for x in objects)], text=True).splitlines()
assert len(object_rows) == 2 * len(selected)
for i, row in enumerate(selected):
    row['object_sha256'] = object_rows[i].split()[0]
    row['object_size_bytes'] = int(object_rows[i+len(selected)].split()[0])
report = dict(branch=subprocess.check_output(['git', 'branch', '--show-current'], text=True).strip(),
    audited_at_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    attempts=len(rows), all_attempts_assigned=True, all_attempts_zero_swaps=True,
    duplicate_source_and_dependencies=0, host_source_digest_mismatches=0,
    current_targets=selected, audited_new_theorems=sum(len(r['axioms']) for r in selected),
    retained_binders_verbatim_after_specialization=retained, conclusion_verbatim_after_specialization=True,
    source_randomness_instances_retained=True, statement_verbatim_in_report=True,
    forbidden_constructs=[], unchanged_sources=unchanged,
    full_frozen_manifest_replayed=False)
(root / 'r1p-final/endpoint-final-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k not in ['current_targets', 'unchanged_sources',
    'retained_binders_verbatim_after_specialization']}, indent=2))
