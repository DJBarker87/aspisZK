#!/usr/bin/env python3
"""Read-only audit of saved R271/R272/R273/R275 publication evidence."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'docs/research/v8-full-view-zk-20260912'
EVID = BASE / 'evidence'
OUT = ROOT / '.r21-scratch/r275-publication-evidence-audit'
FOUNDATIONS = {'propext', 'Classical.choice', 'Quot.sound'}
BUNDLES = {
    'R271': 'r271-current-private-line-norm-bridge',
    'R272': 'r272-current-private-denominator-norm',
    'R273': 'r273-current-private-coefficient-fallback',
    'R275': 'r275-current-private-coefficient-complete',
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def norm(text):
    return re.sub(r'\s+', ' ', text).strip()

def time_field(text, pattern):
    match = re.search(pattern, text, re.M)
    if not match:
        raise ValueError(f'missing saved metric: {pattern}')
    return match.group(1)

def axioms_from_text(text):
    rows = []
    pat = re.compile(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*?)\])", re.S)
    for match in pat.finditer(text):
        name, claim, deps = match.groups()
        if claim == 'does not depend on any axioms':
            rows.append(f"'{name}' does not depend on any axioms")
        else:
            deps = ', '.join(x.strip() for x in deps.replace('\n', ' ').split(','))
            rows.append(f"'{name}' depends on axioms: [{deps}]")
    return rows

def axioms_file_rows(text):
    return axioms_from_text(text)

report = {
    'audit': 'saved evidence only; no Lean, host execution, or proof reruns',
    'foundation_allowlist': sorted(FOUNDATIONS),
    'bundles': {},
    'retained_failed_attempts': {},
    'failed_checks': [],
}
for label, directory in BUNDLES.items():
    d = EVID / directory
    manifest = json.loads((d / 'manifest.json').read_text())
    checksums = json.loads((d / 'SHA256SUMS.json').read_text())
    actual_files = {p.relative_to(d).as_posix() for p in d.rglob('*')
                    if p.is_file() and p.name != 'SHA256SUMS.json'}
    missing = sorted(set(checksums) - actual_files)
    unlisted = sorted(actual_files - set(checksums))
    mismatches = {
        rel: {'expected': expected, 'actual': sha(d / rel) if (d / rel).is_file() else None}
        for rel, expected in checksums.items()
        if not (d / rel).is_file() or sha(d / rel) != expected
    }
    source_copy = d / 'source' / Path(manifest['target']).name
    promoted = BASE / 'lean' / manifest['target']
    log_path = d / manifest['log']
    log = log_path.read_text(errors='replace')
    observed_axioms = axioms_from_text(log)
    expected_axioms = [norm(x) for x in manifest['complete_print_axioms']]
    axiom_rows = axioms_file_rows((d / 'axioms.txt').read_text())
    runner = (d / 'run_focus.py').read_text()
    metrics = {
        'exit_status': int(time_field(log, r'Exit status: ([0-9]+)')),
        'wall_time': time_field(log, r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)'),
        'peak_rss_kib': int(time_field(log, r'Maximum resident set size \(kbytes\): ([0-9]+)')),
        'swaps': int(time_field(log, r'Swaps: ([0-9]+)')),
    }
    resource = manifest['resources']
    cap_checks = {
        'MemoryHigh_5G': resource.get('MemoryHigh') == '5G' and 'MemoryHigh=5G' in runner,
        'MemoryMax_7G': resource.get('MemoryMax') == '7G' and 'MemoryMax=7G' in runner,
        'MemorySwapMax_zero': resource.get('MemorySwapMax') == 0 and 'MemorySwapMax=0' in runner,
        'TasksMax_128': resource.get('TasksMax') == 128 and 'TasksMax=128' in runner,
        'Lean_single_job_and_memory_flag': '-j1' in runner and '-M4500' in runner and resource.get('flags') == '-j1 -M4500',
    }
    metrics_match = all([
        metrics['exit_status'] == manifest['exit_status'],
        metrics['wall_time'] == manifest['wall_time'],
        metrics['peak_rss_kib'] == manifest['peak_rss_kib'],
        metrics['swaps'] == manifest['swaps'],
    ])
    source_match = source_copy.is_file() and promoted.is_file() and source_copy.read_bytes() == promoted.read_bytes()
    source_hash_match = source_copy.is_file() and sha(source_copy) == manifest['source_sha256']
    axiom_match = observed_axioms == expected_axioms and axiom_rows == expected_axioms
    foundations = sorted({dep.strip() for row in observed_axioms
                          for dep in re.findall(r'axioms: \[(.*?)\]', row)
                          for dep in dep.split(',')})
    standard_foundations_only = set(foundations) <= FOUNDATIONS and 'sorryAx' not in log and 'native_decide' not in log
    bundle = {
        'target': manifest['target'],
        'source_revision': manifest['source_revision'],
        'source_revision_consistent': manifest['source_revision'] == '9dacc9b7a141bdf618136511a4ec783a3983245e',
        'source_copy_sha256': sha(source_copy) if source_copy.is_file() else None,
        'promoted_target_sha256': sha(promoted) if promoted.is_file() else None,
        'source_copy_equals_promoted_target': source_match,
        'manifest_source_hash_matches_copy': source_hash_match,
        'checksums': {'listed': len(checksums), 'missing': missing, 'unlisted': unlisted, 'mismatches': mismatches},
        'compile_metrics': {'manifest': {k: manifest[k] for k in ('exit_status', 'wall_time', 'peak_rss_kib', 'swaps')}, 'observed': metrics, 'match': metrics_match},
        'axioms': {'expected_count': len(expected_axioms), 'observed_count': len(observed_axioms), 'manifest_and_file_match_log': axiom_match, 'foundations': foundations, 'standard_foundations_only': standard_foundations_only, 'observed': observed_axioms},
        'runner': {'sha256': sha(d / 'run_focus.py'), 'mentions_saved_remote_workspace': '/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a' in runner, 'resource_caps': cap_checks, 'all_caps_match': all(cap_checks.values())},
        'lean_version': manifest.get('lean_version'),
        'memory_boundary': manifest.get('memory_boundary'),
    }
    bundle['checksums_pass'] = not missing and not unlisted and not mismatches
    bundle['pass'] = all([bundle['checksums_pass'], source_match, source_hash_match, metrics_match, axiom_match, standard_foundations_only, bundle['runner']['all_caps_match'], bundle['source_revision_consistent']])
    report['bundles'][label] = bundle

# Preserve R273's three failed proof attempts as distinct recorded events.
r273 = EVID / BUNDLES['R273']
rej = []
for log_rel in [
    'rejected/aspis-focus-1790914436088618000.log',
    'rejected/aspis-focus-1790914493556814000.log',
    'rejected/aspis-focus-1790914524973347000.log',
]:
    text = (r273 / log_rel).read_text(errors='replace')
    first_error = next((line.strip() for line in text.splitlines() if 'error' in line.lower()), '')
    rej.append({'log': log_rel, 'exit_status': int(time_field(text, r'Exit status: ([0-9]+)')), 'first_error_line': first_error, 'sorryAx_present': 'sorryAx' in text, 'retained_and_checksummed': log_rel in json.loads((r273 / 'SHA256SUMS.json').read_text())})
report['retained_failed_attempts']['R273'] = {
    'readme_summary': (r273 / 'rejected/README.md').read_text().strip(),
    'attempts': rej,
    'three_distinct_attempts_retained': len(rej) == 3 and len({x['log'] for x in rej}) == 3,
    'all_exit_nonzero': all(x['exit_status'] != 0 for x in rej),
    'all_retained_and_checksummed': all(x['retained_and_checksummed'] for x in rej),
}

# R275's earlier failure was a missing compiled R273 prerequisite, distinct from a theorem failure.
r275 = EVID / BUNDLES['R275']
prereq_rel = 'rejected/aspis-focus-1790914664140021000.log'
prereq_text = (r275 / prereq_rel).read_text(errors='replace')
report['retained_failed_attempts']['R275_prerequisite'] = {
    'log': prereq_rel,
    'exit_status': int(time_field(prereq_text, r'Exit status: ([0-9]+)')),
    'missing_R273_object_reported': 'R273PrivateCoefficientFallback.olean' in prereq_text and 'does not exist' in prereq_text,
    'retained_and_checksummed': prereq_rel in json.loads((r275 / 'SHA256SUMS.json').read_text()),
    'README_classification': (r275 / 'rejected/README.md').read_text().strip(),
    'separate_from_R273_proof_failures': True,
}

for label, bundle in report['bundles'].items():
    if not bundle['pass']:
        report['failed_checks'].append(f'{label} saved evidence bundle checks')
if not report['retained_failed_attempts']['R273']['three_distinct_attempts_retained'] or not report['retained_failed_attempts']['R273']['all_exit_nonzero'] or not report['retained_failed_attempts']['R273']['all_retained_and_checksummed']:
    report['failed_checks'].append('R273 failed attempts retained distinctly')
if report['retained_failed_attempts']['R275_prerequisite']['exit_status'] == 0 or not report['retained_failed_attempts']['R275_prerequisite']['missing_R273_object_reported'] or not report['retained_failed_attempts']['R275_prerequisite']['retained_and_checksummed']:
    report['failed_checks'].append('R275 prerequisite failure classification')
report['status'] = 'PASS' if not report['failed_checks'] else 'FAIL'
(OUT / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
lines = ['# R271–R275 saved evidence audit', '', report['audit'], '', f"Audit result: **{report['status']}**.", '', 'Each accepted bundle is checked for inventory and SHA-256 consistency, equality of the saved source copy and promoted target, source hash, saved exit/wall/RSS/swap metrics, full axiom output against both manifest and `axioms.txt`, foundation names, pinned revision, and runner resource/Lean flags.', '', '| Target | Copy and checksums | Metrics | Axiom reports | Runner caps | Result |', '|---|---:|---:|---:|---:|---:|']
for label, b in report['bundles'].items():
    lines.append(f"| {label} | {'pass' if b['source_copy_equals_promoted_target'] and b['checksums_pass'] else 'fail'} | {'pass' if b['compile_metrics']['match'] else 'fail'} | {b['axioms']['observed_count']} / {'pass' if b['axioms']['manifest_and_file_match_log'] and b['axioms']['standard_foundations_only'] else 'fail'} | {'pass' if b['runner']['all_caps_match'] else 'fail'} | {'pass' if b['pass'] else 'fail'} |")
lines += ['', 'R271, R272, R273, and R275 use the saved source revision `9dacc9b7a141bdf618136511a4ec783a3983245e`. Their runners record `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`. Full per-target values and axiom declarations are in `audit.json.', '', 'R273 retains three distinct failed proof runs, each with nonzero status and a checksummed log. R275 retains a separate prerequisite failure: its earlier run could not find the compiled R273 object. This is recorded as a dependency/setup failure, not conflated with the three R273 theorem-proof attempts.', '', 'This audit reports saved evidence integrity and metadata only. It does not rerun Lean or decide whether any proof closes a semantic or release obligation.', '']
(OUT / 'README.md').write_text('\n'.join(lines))
print(json.dumps({'status': report['status'], 'failed_checks': report['failed_checks'], 'bundles': {k: {'pass': v['pass'], 'axioms': v['axioms']['observed_count'], 'checksums': v['checksums_pass'], 'metrics': v['compile_metrics']['match']} for k, v in report['bundles'].items()}, 'retained_failures': report['retained_failed_attempts']}, indent=2))
if report['failed_checks']:
    raise SystemExit(1)
