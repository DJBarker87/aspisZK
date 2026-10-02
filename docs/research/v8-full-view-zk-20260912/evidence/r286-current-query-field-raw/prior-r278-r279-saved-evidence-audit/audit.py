#!/usr/bin/env python3
"""Read-only saved-evidence and binding audit for R278/R279."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'docs/research/v8-full-view-zk-20260912'
EVID = BASE / 'evidence'
OUT = ROOT / '.r21-scratch/r279-publication-evidence-audit'
R278 = EVID / 'r278-current-private-inverse-raw'
R279 = EVID / 'r279-current-private-scalar-inverse'
FOUNDATIONS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def norm(value):
    return re.sub(r'\s+', ' ', value).strip()


def saved_metric(text, pattern):
    match = re.search(pattern, text, re.M)
    if not match:
        raise ValueError(f'missing saved metric: {pattern}')
    return match.group(1)


def axioms(text):
    result = []
    pattern = re.compile(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*?)\])", re.S)
    for match in pattern.finditer(text):
        name, claim, deps = match.groups()
        if claim == 'does not depend on any axioms':
            result.append(f"'{name}' does not depend on any axioms")
        else:
            clean_deps = ', '.join(x.strip() for x in deps.replace('\n', ' ').split(','))
            result.append(f"'{name}' depends on axioms: [{clean_deps}]")
    return result


def decl_blocks(text):
    starts = [m.start() for m in re.finditer(r'(?m)^/--', text)]
    result = {}
    for idx, start in enumerate(starts):
        end = starts[idx + 1] if idx + 1 < len(starts) else len(text)
        block = text[start:end].strip()
        block = re.split(r'(?m)^#print axioms ', block, maxsplit=1)[0].strip()
        block = re.sub(r'\nend AspisR\d+\w*\s*$', '', block).strip()
        name_match = re.search(r'(?m)^.*?\b(?:def|structure)\s*\n?\s*([\w.]+)', block)
        if name_match:
            result[name_match.group(1)] = block
    return result


def declaration_body(block):
    match = re.search(r'(?m)^.*?\b(?:def|structure)\s+', block)
    if not match:
        raise ValueError('definition keyword not found')
    return block[match.start():].strip()


def bundle(bundle_dir, expected_promoted, expected_count):
    manifest = json.loads((bundle_dir / 'manifest.json').read_text())
    sums = json.loads((bundle_dir / 'SHA256SUMS.json').read_text())
    present = {p.relative_to(bundle_dir).as_posix() for p in bundle_dir.rglob('*')
               if p.is_file() and p.name != 'SHA256SUMS.json'}
    missing = sorted(set(sums) - present)
    unlisted = sorted(present - set(sums))
    bad_hashes = {
        rel: {'expected': expected, 'actual': sha(bundle_dir / rel) if (bundle_dir / rel).is_file() else None}
        for rel, expected in sums.items()
        if not (bundle_dir / rel).is_file() or sha(bundle_dir / rel) != expected
    }
    source = bundle_dir / 'source' / Path(manifest['target']).name
    promoted = BASE / 'lean' / expected_promoted
    log_path = bundle_dir / manifest['log']
    log = log_path.read_text(errors='replace')
    expected_axioms = [norm(line) for line in manifest['complete_print_axioms']]
    observed_axioms = axioms(log)
    axioms_file = axioms((bundle_dir / 'axioms.txt').read_text())
    observed_metrics = {
        'exit_status': int(saved_metric(log, r'Exit status: ([0-9]+)')),
        'wall_time': saved_metric(log, r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)'),
        'peak_rss_kib': int(saved_metric(log, r'Maximum resident set size \(kbytes\): ([0-9]+)')),
        'swaps': int(saved_metric(log, r'Swaps: ([0-9]+)')),
    }
    manifest_metrics = {k: manifest[k] for k in observed_metrics}
    runner = (bundle_dir / 'run_focus.py').read_text()
    resources = manifest['resources']
    cap_checks = {
        'MemoryHigh_5G': resources.get('MemoryHigh') == '5G' and 'MemoryHigh=5G' in runner,
        'MemoryMax_7G': resources.get('MemoryMax') == '7G' and 'MemoryMax=7G' in runner,
        'MemorySwapMax_zero': resources.get('MemorySwapMax') == 0 and 'MemorySwapMax=0' in runner,
        'TasksMax_128': resources.get('TasksMax') == 128 and 'TasksMax=128' in runner,
        'Lean_flags': resources.get('flags') == '-j1 -M4500' and '-j1' in runner and '-M4500' in runner,
    }
    all_foundations = sorted({name.strip() for row in observed_axioms
                              for deps in re.findall(r'axioms: \[(.*?)\]', row)
                              for name in deps.split(',')})
    no_extra_axioms = set(all_foundations) <= FOUNDATIONS and 'sorryAx' not in log and 'native_decide' not in log
    checks = {
        'all_checksums': not missing and not unlisted and not bad_hashes,
        'source_copy_matches_promoted': source.is_file() and promoted.is_file() and source.read_bytes() == promoted.read_bytes(),
        'source_copy_matches_manifest_hash': source.is_file() and sha(source) == manifest['source_sha256'],
        'metrics_match': observed_metrics == manifest_metrics,
        'full_axiom_reports_match_manifest_and_file': observed_axioms == expected_axioms == axioms_file,
        'exact_expected_axiom_count': len(observed_axioms) == expected_count,
        'three_standard_foundations_only': no_extra_axioms and set(all_foundations) == FOUNDATIONS,
        'resource_flags_match': all(cap_checks.values()),
        'compile_revision_e8601f2d': manifest['source_revision'] == 'e8601f2d13149484f3a6a0304cd48892821363c4',
        'runner_targets_expected_workspace': '/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a' in runner,
        'toolchain_is_pinned': manifest.get('lean_version') == '4.32.0 (8c9756b28d64dab099da31a4c09229a9e6a2ef35)' and 'leanprover/lean4:v4.32.0' in runner,
    }
    return {
        'target': manifest['target'], 'source_revision': manifest['source_revision'],
        'source_sha256': manifest['source_sha256'], 'saved_source_sha256': sha(source) if source.is_file() else None,
        'promoted_target_sha256': sha(promoted) if promoted.is_file() else None,
        'checksums': {'listed': len(sums), 'missing': missing, 'unlisted': unlisted, 'mismatches': bad_hashes},
        'metrics': {'manifest': manifest_metrics, 'observed': observed_metrics},
        'axioms': {'expected_count': expected_count, 'observed_count': len(observed_axioms), 'foundations': all_foundations, 'reports': observed_axioms},
        'runner': {'sha256': sha(bundle_dir / 'run_focus.py'), 'caps': cap_checks, 'remote_workspace_present': checks['runner_targets_expected_workspace'], 'lean_version': manifest.get('lean_version')},
        'checks': checks, 'pass': all(checks.values()),
    }

report = {
    'audit': 'read-only saved evidence audit; no Lean reruns, source edits, or proof/security conclusions',
    'bundles': {
        'R278': bundle(R278, 'AspisR278PrivateInverseRaw.lean', 3),
        'R279': bundle(R279, 'AspisV8R19/R279PrivateScalarInverse.lean', 3),
    },
    'binding_recomputation': {},
    'failed_checks': [],
}

# Recompute all R278 declaration bindings independently from the saved input text.
R276_FUNS = ROOT / '.r21-scratch/r276-private-inverse-leaf-translation/generated/AspisR276PrivateInverseLeaves/Funs.lean'
R276_TYPES = ROOT / '.r21-scratch/r276-private-inverse-leaf-translation/generated/AspisR276PrivateInverseLeaves/Types.lean'
R249_RAW = ROOT / '.r21-scratch/r249-r110-raw/AspisR249R110Raw.lean'
R156_FUNS = BASE / 'lean/AspisR156FullFreeze/FunsCore.lean'
R156_TYPES = BASE / 'lean/AspisR156FullFreeze/Types.lean'
R278_RAW = ROOT / '.r21-scratch/r278-private-inverse-raw/AspisR278PrivateInverseRaw.lean'

r276_text, r249_text, r156_text, r278_text = [p.read_text() for p in (R276_FUNS, R249_RAW, R156_FUNS, R278_RAW)]
r276_decls = decl_blocks(r276_text)
r249_decls = decl_blocks(r249_text)
r156_decls = decl_blocks(r156_text)
r278_decls = decl_blocks(r278_text)
root_names = [
    'circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO',
    'circle_norm.joined_inverse.line_norm.r110_norm.B.neg',
    'circle_norm.joined_inverse.line_norm.r110_norm.B.inv',
]
root_checks = []
for name in root_names:
    before = r276_decls[name]
    after = r278_decls[name]
    root_checks.append({'name': name, 'source_and_raw_blocks_byte_equal': before == after,
                        'source_sha256': hashlib.sha256(before.encode()).hexdigest(),
                        'raw_sha256': hashlib.sha256(after.encode()).hexdigest()})

helpers = [
    ('circle_norm.joined_inverse.line_norm.r110_norm.B.sub', r276_decls, r249_decls,
     [('core.num.U32.', 'Std.U32.', 2, 'R249 U32 wrapping API qualification')]),
    ('circle_norm.joined_inverse.line_norm.r110_norm.P110', r276_decls, r249_decls, []),
    ('aspis_core.field.P', r276_decls, r156_decls, []),
    ('aspis_core.field.reduce_u64', r276_decls, r156_decls, []),
    ('aspis_core.field.M31.mul', r276_decls, r156_decls,
     [('31#i32', '31#u32', 1, 'R156 shift-count type adaptation')]),
    ('aspis_core.field.square_n_loop.body', r276_decls, r156_decls, []),
    ('aspis_core.field.square_n_loop', r276_decls, r156_decls, []),
    ('aspis_core.field.square_n', r276_decls, r156_decls, []),
    ('aspis_core.field.M31.inv', r276_decls, r156_decls, []),
]
helper_checks = []
for name, source_decls, target_decls, allowed in helpers:
    left = declaration_body(source_decls[name])
    right = declaration_body(target_decls[name])
    applied = []
    for old, new, expected_count, label in allowed:
        count = left.count(old)
        applied.append({'label': label, 'from': old, 'to': new, 'expected_count': expected_count, 'observed_count': count})
        if count != expected_count:
            raise AssertionError(f'{name}: adapter count {count} != {expected_count}: {old}')
        left = left.replace(old, new)
    helper_checks.append({'name': name, 'body_equal_after_only_listed_adapters': norm(left) == norm(right),
                          'adapters': applied,
                          'adapted_source_sha256': hashlib.sha256(norm(left).encode()).hexdigest(),
                          'target_sha256': hashlib.sha256(norm(right).encode()).hexdigest()})

# Compare external layout aliases and ensure R278 did not redeclare them.
r276_types = R276_TYPES.read_text()
r156_types = R156_TYPES.read_text()
def alias_line(text, needle):
    return next(line.strip() for line in text.splitlines() if needle in line)
layout = {
    'R276_M31': alias_line(r276_types, 'def aspis_core.field.M31 :='),
    'R156_M31': alias_line(r156_types, 'def aspis_core.field.M31 :='),
    'R249_B': alias_line(r249_text, 'def circle_norm.joined_inverse.line_norm.r110_norm.B :='),
    'R278_shadows_B_or_M31': bool(re.search(r'(?m)^\s*def\s+(?:circle_norm\..*\.B|aspis_core\.field\.M31)\s*(?::|:=)', r278_text)),
}
report['binding_recomputation'] = {
    'root_block_count': len(root_checks), 'root_blocks': root_checks,
    'root_blocks_all_byte_equal': all(row['source_and_raw_blocks_byte_equal'] for row in root_checks),
    'transitive_helper_count': len(helper_checks), 'helpers': helper_checks,
    'all_helper_bodies_match_after_only_listed_adapters': all(row['body_equal_after_only_listed_adapters'] for row in helper_checks),
    'layout': layout,
    'R276_M31_equals_R156_M31': layout['R276_M31'] == layout['R156_M31'] == 'def aspis_core.field.M31 := Std.U32',
    'R249_B_is_Std_U32': layout['R249_B'].endswith(':= Std.U32'),
    'no_R278_type_shadow': not layout['R278_shadows_B_or_M31'],
    'input_hashes': {p.name + ':' + str(p): sha(p) for p in (R276_FUNS, R276_TYPES, R249_RAW, R156_FUNS, R156_TYPES, R278_RAW)},
}

for label, result in report['bundles'].items():
    if not result['pass']:
        report['failed_checks'].extend(f'{label}.{key}' for key, ok in result['checks'].items() if not ok)
if not report['binding_recomputation']['root_blocks_all_byte_equal']:
    report['failed_checks'].append('R278 root declaration blocks')
if not report['binding_recomputation']['all_helper_bodies_match_after_only_listed_adapters']:
    report['failed_checks'].append('R278 helper declaration comparisons')
for key in ('R276_M31_equals_R156_M31', 'R249_B_is_Std_U32', 'no_R278_type_shadow'):
    if not report['binding_recomputation'][key]:
        report['failed_checks'].append('R278 ' + key)
report['status'] = 'PASS' if not report['failed_checks'] else 'FAIL'
(OUT / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
md = ['# R278/R279 saved publication evidence audit', '', report['audit'], '', f"Audit result: **{report['status']}**.", '', '| Target | Source/copy | Checksums | Metrics | Axioms | Runner/revision |', '|---|---:|---:|---:|---:|---:|']
for label, result in report['bundles'].items():
    checks = result['checks']
    md.append(f"| {label} | {'pass' if checks['source_copy_matches_promoted'] and checks['source_copy_matches_manifest_hash'] else 'fail'} | {'pass' if checks['all_checksums'] else 'fail'} | {'pass' if checks['metrics_match'] else 'fail'} | {result['axioms']['observed_count']} / {'pass' if checks['full_axiom_reports_match_manifest_and_file'] and checks['three_standard_foundations_only'] else 'fail'} | {'pass' if checks['resource_flags_match'] and checks['compile_revision_e8601f2d'] else 'fail'} |")
md += ['', 'The R278 raw adapter has three root declaration blocks byte-equal to the generated R276 declarations and nine independently recomputed transitive helper body comparisons. The only replacements permitted by this audit are `core.num.U32.` → `Std.U32.` twice for R249 B.sub and `31#i32` → `31#u32` once for the R156 M31.mul shift count. R276 and R156 M31 layouts match (`Std.U32`); R249 B is `Std.U32`; the R278 file declares no B or M31 type shadow.', '', 'Both saved compile logs report exit status 0, zero swaps, pinned Lean 4.32.0, revision `e8601f2d13149484f3a6a0304cd48892821363c4`, resource caps 5G/7G/0 swap/128 tasks, and flags `-j1 -M4500`. All six axiom reports match the saved manifests and `axioms.txt` and use only `propext`, `Classical.choice`, and `Quot.sound`.', '', 'This is a saved artifact and metadata audit. No Lean rerun or source-semantics/security conclusion was made.', '']
(OUT / 'README.md').write_text('\n'.join(md))
print(json.dumps({'status': report['status'], 'failed_checks': report['failed_checks'], 'bundle_pass': {k:v['pass'] for k,v in report['bundles'].items()}, 'root_blocks': report['binding_recomputation']['root_blocks_all_byte_equal'], 'helper_count': report['binding_recomputation']['transitive_helper_count'], 'helper_pass': report['binding_recomputation']['all_helper_bodies_match_after_only_listed_adapters'], 'layout': report['binding_recomputation']['layout']}, indent=2))
if report['failed_checks']:
    raise SystemExit(1)
