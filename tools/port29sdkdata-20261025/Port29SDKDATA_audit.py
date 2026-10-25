#!/usr/bin/env python3
"""Read-only graph/provenance audit. Never opens historical CURRENT cache paths."""
import collections
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import uuid

ROOT = Path(__file__).resolve().parents[2]
E = ROOT / 'evidence/port29sdkdata-20261025'
OLD = Path('/private/tmp/port28rootexport-20261024-2e053459f91b43c3b4c640d575d607c9')
CURRENT = Path('/private/tmp/s126-sdk-current-9acc-proof-refresh-20261024-v1')
A = '0d373458d3'
P18 = '904745b496'
BASE = 'docs/research/100bit-spend-path-20261013/'


def pin(p):
    p = Path(p)
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return dict(path=str(p), bytes=p.stat().st_size, sha256=h.hexdigest())


def git_bytes(rev, path):
    return subprocess.check_output(['git', 'show', rev + ':' + path], cwd=ROOT)


def write(p, data):
    with Path(p).open('x') as f:
        json.dump(data, f, indent=2)
        f.write('\n')


def closure(seeds, graph):
    seen = set()
    pending = list(seeds)
    while pending:
        n = pending.pop()
        if n in seen:
            continue
        seen.add(n)
        pending.extend(graph.get(n, set()) - seen)
    return seen


def main():
    begin = time.monotonic()
    out = Path('/private/tmp/Port29SDKDATA-' + uuid.uuid4().hex)
    out.mkdir(mode=0o700)
    source_revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    gitpins = []

    def immutable(rev, path):
        b = git_bytes(rev, path)
        gitpins.append(dict(revision=rev, path=path, bytes=len(b), sha256=hashlib.sha256(b).hexdigest()))
        return json.loads(b)

    release = immutable(A, BASE + 'evidence/s126-current-caller-20261021/sdk-current-export-20261024/release.json')
    manifest = immutable(A, BASE + 'evidence/s126-current-caller-20261021/sdk-current-export-20261024/release-manifest.json')
    mp = pin(CURRENT / 'manifest.json')
    assert mp['sha256'] == release['manifest_sha256'] == 'e55b656c8c5abb11c769f4a5c6b5e5ab574e061b437a26240c2c65c25c542226'
    assert (CURRENT / 'manifest.json').read_bytes() == git_bytes(A, BASE + 'evidence/s126-current-caller-20261021/sdk-current-export-20261024/release-manifest.json')
    observed = []

    def verify(p, expected):
        p = Path(p)
        assert not p.is_symlink() and p.is_file(), str(p)
        x = pin(p)
        assert x['sha256'] == expected['sha256'] and x['bytes'] == expected['bytes'], str(p)
        observed.append(x)
        return x

    for f in manifest['files']:
        rel = Path(f['relative'])
        assert not rel.is_absolute() and '..' not in rel.parts
        p = CURRENT / rel
        assert p.stat().st_mode & 0o222 == 0, str(p)
        verify(p, f)
    assert CURRENT.stat().st_mode & 0o222 == 0
    original_audit_pin = pin(OLD / 'correction-output-audit.json')
    assert original_audit_pin['sha256'] == '66bb1588c5596e5de11a5b756727e2e21c0ba9bac388dddfd4aca9bdab4bee36'
    observed.append(original_audit_pin)
    old = json.loads((OLD / 'correction-output-audit.json').read_text())
    dp = old['reused_input_manifest']
    verify(dp['path'], dp)
    diagnostic = json.loads(Path(dp['path']).read_text())
    for f in diagnostic['object_parts']:
        # Only the already retained copy is authorized, never its remote provenance path.
        p = Path(f['retained_path'])
        assert str(p).startswith('/private/tmp/port28rootexport-20261024-')
        verify(p, f)
    for f in old['final_round_transports']:
        assert Path(f['path']).is_relative_to(OLD / 'transports')
        verify(f['path'], f)
    for f in diagnostic['inputs']:
        verify(f['path'], f)
    # Complete part hashes, including server/private: hashes are NOT name inventories.
    for f in diagnostic['core_parts'] + diagnostic['runtime']:
        assert str(f['path']).startswith('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/')
        verify(f['path'], f)

    canonical = immutable(P18, 'evidence/port18coherence-20261024/canonical-manifest.json')
    p18manifest = immutable(P18, 'evidence/port18coherence-20261024/manifest.json')
    cp = next(p for p in gitpins if p['path'].endswith('/canonical-manifest.json'))
    assert cp['sha256'] == p18manifest['canonical_manifest_sha256']
    p18names = {d['name']: d['origin'] for d in canonical['declarations']}
    p18modules = {(d['side'], d['module']): d for d in canonical['modules']}
    assert len(p18names) == 15241
    # No Port18 runtime/cache/object payload is opened in this noncompiler stage.
    old_modules = collections.defaultdict(list)
    for f in diagnostic['object_parts']:
        old_modules[(str(f['root_index']), f['module'])].append(f)

    def full_part_matches(module):
        if not module:
            return []
        targets = {Path(f['path']).name: (f['sha256'], f['bytes'])
                   for f in module['original_objects']
                   if '.olean' in Path(f['path']).name}
        if not targets:
            return []
        matches = []
        for (origin, name), fs in old_modules.items():
            if name != module['module']:
                continue
            actual = {Path(f['path']).name: (f['sha256'], f['bytes']) for f in fs}
            if actual == targets:
                matches.append(dict(origin=origin, module=name, parts=[dict(path=f['retained_path'], sha256=f['sha256'], bytes=f['bytes']) for f in fs]))
        return matches

    original = collections.defaultdict(list)
    og = collections.defaultdict(set)
    for row in old['edges']:
        original[row['name']].append(row)
        og[row['name']].update(row['dependencies'])
    current = collections.defaultdict(list)
    cg = collections.defaultdict(set)
    with (CURRENT / 'constants.jsonl').open() as f:
        for line in f:
            row = json.loads(line)
            current[row['name']].append(row)
            cg[row['name']].update(row['dependencies'])
    # Edges log includes exporter selection events; normalize repetitions, require exact final sets.
    eg = collections.defaultdict(set)
    with (CURRENT / 'edges.jsonl').open() as f:
        for line in f:
            m, n, ds = json.loads(line)
            eg[n].update(ds)
    assert dict(eg) == dict(cg)
    assert len(current) == manifest['constant_count'] == 27287
    assert not (set().union(*cg.values()) - current.keys())
    assert not manifest['unresolved'] and not manifest['nonidentical_current_duplicates']
    seeds = {line.split('\t')[1] for line in (OLD / 'seeds.tsv').read_text().splitlines()}
    assert len(seeds) == 67 and seeds <= original.keys()
    required = seeds | set().union(*og.values())
    core = set(old['core_leaves'])
    missing = required - original.keys() - core
    assert missing == set(old['unresolved_recomputed']) == set(old['unresolved_emitted']) and len(missing) == 323
    old_reach = closure(seeds, og)
    all_seeds = set(seeds)
    audit_input = json.loads((CURRENT / 'audit-input.json').read_text())
    current_seeds = set(audit_input['seeds'])
    # CURRENT seeds are an array of names; deliberately preserve the flagged raw auxiliary.
    assert all(isinstance(n, str) for n in current_seeds)
    assert len(current_seeds) == manifest['seed_count']
    all_seeds.update(current_seeds)
    union = collections.defaultdict(set)
    for g in (og, cg):
        for n, ds in g.items():
            union[n].update(ds)
    union_reach = closure(all_seeds, union)
    union_known = set(original) | set(current)
    raw_gaps = union_reach - union_known
    observed_leaf_gaps = raw_gaps & core
    residual_gaps = raw_gaps - core
    request = json.loads((CURRENT / 'metadata/request.json').read_text())
    current_inputs = json.loads((CURRENT / 'metadata/input-pins-v2.json').read_text())
    current_input_map = {r['module']: r for r in current_inputs['inputs']}
    root_selected = collections.defaultdict(list)
    for f in old['final_round_transports']:
        for n in f['names']:
            root_selected[n].append({k: f[k] for k in ['origin', 'module', 'path', 'sha256', 'bytes']})

    rows = []
    for n in sorted(missing):
        cs = current.get(n, [])
        origin = p18names.get(n)
        pm = p18modules.get(tuple(origin.split(':', 1))) if origin else None
        matches = full_part_matches(pm)
        modules = sorted({r['module'] for r in cs})
        if modules:
            if all(m.startswith(('Init.', 'Lean.', 'Std.')) or m in ['Init', 'Lean', 'Std'] for m in modules):
                provenance = 'standard-core CURRENT raw declaration available'
            elif all(m.startswith('Mathlib.') for m in modules):
                provenance = 'Mathlib library CURRENT raw declaration available'
            elif all(m.startswith('Aeneas.') for m in modules):
                provenance = 'Aeneas library CURRENT raw declaration available'
            else:
                provenance = 'project CURRENT raw declaration available'
        else:
            provenance = 'not in CURRENT selected raw transports'
        rows.append(dict(name=n, provenance=provenance, current_modules=modules,
                         current_body_authority=[dict(module=m, selected_input=current_input_map.get(m),
                             transport=str(CURRENT / 'transport' / (m.replace('.', '/') + '.olean')),
                             assessment='Published CURRENT body only; no old/full-declaration equality inferred') for m in modules],
                         port18_released_manifest_origin=origin,
                         port18_source_authority=pm.get('source') if pm else None,
                         original_full_part_pin_matches=matches,
                         availability=('ORIGINAL module pins match released Port18 declaration provenance; raw extraction still needed' if matches else
                                       'CURRENTONLY selected-data candidate; original full parts not name-inventoried' if cs else
                                       'releasedPort18 manifest only; original-part agreement not established' if origin else
                                       'absent from both selected-data name lists; original/core full-part names NOT inventoried'),
                         old_name_absence_proved=False, strict_sameDeclaration='NOT RUN',
                         reachable_from_root_67=n in old_reach,
                         incoming_original=[dict(origin=r['origin'], module=r['module'], name=r['name'])
                                            for r in old['edges'] if n in r['dependencies']]))
    write(E / 'Port29SDKDATA_missing-323.json', rows)
    pairs = []
    for n in sorted(set(original) & set(current)):
        pairs.append(dict(name=n, root_origins=root_selected[n], current_modules=sorted({x['module'] for x in current[n]}),
                          dependency_sets_equal=og[n] == cg[n], strict_sameDeclaration='NOT RUN; edge equality is not declaration equality'))
    write(out / 'Port29SDKDATA_pair-candidates.json', pairs)
    # Preserve all origin edges. No first-wins and no declaration/body selection here.
    with (out / 'Port29SDKDATA_cross-origin-edges.jsonl').open('x') as f:
        for side, data in [('ORIGINAL', original), ('CURRENT', current)]:
            for n, rs in data.items():
                for r in rs:
                    f.write(json.dumps(dict(side=side, **r), separators=(',', ':')) + '\n')
    write(out / 'Port29SDKDATA_union-worklist.json', dict(
        seeds=sorted(all_seeds), reachable=sorted(union_reach), raw_missing=sorted(raw_gaps),
        prior_main_core_leaves_without_body=sorted(observed_leaf_gaps), residual=sorted(residual_gaps),
        semantics='Conservative graph union includes both origins at common names, not an accepted declaration selection or safe closure'))
    # Record full observed pins outside Git, then verify every input again without mutating donors.
    write(out / 'Port29SDKDATA_input-pins.json', observed)
    for x in observed:
        assert pin(x['path']) == x, x['path']
    outputs = [pin(p) for p in sorted(out.iterdir())]
    stats = dict(
        schema='Port29SDKDATA-noncompiler-graph-provenance-v1', status='DATA AUDIT PASS; required full-part/declaration diagnostic pending',
        source_revision=source_revision, command=[sys.executable, '-B', str(Path(__file__).resolve())],
        tool=pin(__file__), python=dict(version=sys.version, executable=pin(Path(sys.executable).resolve())),
        immutable_git_inputs=gitpins, current_release_manifest=mp, original_audit_manifest=original_audit_pin,
        pre_post_pins_unchanged=True, pinned_file_observations=len(observed), pinned_bytes=sum(x['bytes'] for x in observed),
        retained_outputs=outputs, missing_323=pin(E / 'Port29SDKDATA_missing-323.json'),
        original=dict(seeds=len(seeds), selected_unique=len(original), origin_entries=sum(map(len, original.values())),
                      required=len(required), observed_main_core_leaves=len(core), unresolved=len(missing),
                      seed_reachable=len(old_reach), seed_reachable_unresolved=len(old_reach & missing)),
        current=dict(constants=len(current), seeds=len(current_seeds), missing_dependencies=0,
                     strict_duplicates_reused=manifest['duplicate_count'], strict_duplicate_validation='Reused owner raw audit; payload hashes newly verified, not a new sameDeclaration check'),
        missing_availability_counts=dict(collections.Counter(r['availability'] for r in rows)),
        missing_provenance_counts=dict(collections.Counter(r['provenance'] for r in rows)),
        missing_current_available=sum(bool(r['current_modules']) for r in rows),
        missing_port18_manifest_available=sum(r['port18_released_manifest_origin'] is not None for r in rows),
        original_module_pin_matched_missing=sum(bool(r['original_full_part_pin_matches']) for r in rows),
        pair_candidates=len(pairs), edge_different_pairs=sum(not r['dependency_sets_equal'] for r in pairs),
        root_duplicate_groups=len(old['duplicate_name_origins']), root_strict_duplicates='NOT RUN; containing-transport byte equality is not substituted',
        proposed_union=dict(seeds=len(all_seeds), reachable=len(union_reach), raw_missing=len(raw_gaps),
                            prior_core_leaf_body_missing=len(observed_leaf_gaps), residual=len(residual_gaps), residual_names=sorted(residual_gaps),
                            selected_unique=len(union_known), fixed_point=True,
                            safe_logical_closure=False, declaration_selection_accepted=False),
        raw_flagged_auxiliary='AspisR1.S2W_D189Wrappers.reserve._unsafe_rec',
        raw_auxiliary_reachable_from_root67='AspisR1.S2W_D189Wrappers.reserve._unsafe_rec' in old_reach,
        raw_auxiliary_reachable_from_combined_raw_seeds='AspisR1.S2W_D189Wrappers.reserve._unsafe_rec' in union_reach,
        core_part_hash_inventory=dict(count=len(diagnostic['core_parts']),
            parts=dict(collections.Counter('private' if x['path'].endswith('.private') else 'server' if x['path'].endswith('.server') else 'main' for x in diagnostic['core_parts'])),
            complete_names_types_values='NOT INVENTORIED; requires held raw diagnostic'),
        original_part_hash_inventory=dict(count=len(diagnostic['object_parts']), modules=len(old_modules)),
        proof_overlay=release['proof_refresh'], overlay_changes=current_inputs['changes'],
        primary_source_targets=request['targets'],
        no_new_theorem=True, print_axioms='N/A: noncompiler data audit; no theorem or kernel reconstruction',
        lean_invocations=0, pending_diagnostics=2, global_actual_unchanged=349, global_ceiling=368,
        absent_required_rules='/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/local-lean.txt',
        exit_status=0, wall_seconds=time.monotonic()-begin,
        peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap)
    assert stats['peak_rss_bytes'] < 512 * 1024**2
    write(E / 'Port29SDKDATA_audit.json', stats)
    print(json.dumps({k:stats[k] for k in ['status','missing_current_available','missing_port18_manifest_available','original_module_pin_matched_missing','pair_candidates','edge_different_pairs','missing_availability_counts','missing_provenance_counts','proposed_union','wall_seconds','peak_rss_bytes','swaps']}))


if __name__ == '__main__':
    main()
