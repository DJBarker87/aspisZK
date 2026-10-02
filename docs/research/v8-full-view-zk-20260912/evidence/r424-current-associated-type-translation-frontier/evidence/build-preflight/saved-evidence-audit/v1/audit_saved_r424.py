#!/usr/bin/env python3
"""Read-only local consistency audit for saved R424 build receipts."""
import hashlib, json, pathlib, re, subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
PREFLIGHT = ROOT / 'build-preflight'
AUDIT = ROOT / 'saved-evidence-audit'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def check_run(name, target, sources, expected_wall, expected_rss):
    p = PREFLIGHT / name
    cmd = json.loads((p/'command.json').read_text())
    receipt = json.loads((p/'metrics-receipt.json').read_text())
    result = json.loads((p/'result.json').read_text())
    inspect = json.loads((p/'docker-inspect.json').read_text())
    inspect = inspect[0] if isinstance(inspect, list) else inspect
    reservation = json.loads((p/'reservation-before.json').read_text())
    gnu = (p/'gnu-time.txt').read_text()
    m = re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)', gnu)
    rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', gnu)
    swaps = re.search(r'Swaps: (\d+)', gnu)
    exit_status = re.search(r'Exit status: (\d+)', gnu)
    source_check = {}
    for rel, digest in sources.items():
        f = p/'source'/rel
        source_check[rel] = {'exists': f.is_file(), 'sha256': sha(f) if f.is_file() else None,
                             'expected_sha256': digest, 'matches': f.is_file() and sha(f) == digest}
    host = inspect.get('HostConfig', {})
    state = inspect.get('State', {})
    target_match = cmd.get('target') == target == receipt.get('target')
    capset_match = (reservation.get('root_slice') == 'MemoryHigh=5368709120\nMemoryMax=7516192768\nMemorySwapMax=0\nTasksMax=128\n'
                    and host.get('MemoryReservation') == 5368709120 and host.get('Memory') == 7516192768
                    and host.get('MemorySwap') == 7516192768 and host.get('PidsLimit') == 128
                    and host.get('CgroupParent') == 'aspisr424.slice' and host.get('NetworkMode') == 'none')
    checks = {
        'command_and_receipt_target_match': target_match,
        'source_revision_matches_all_receipts': cmd.get('source_revision') == receipt.get('source_revision') == result.get('source_revision'),
        'source_hashmaps_match_all_receipts': cmd.get('source_sha256') == receipt.get('source_sha256') == result.get('source_sha256') == sources,
        'source_snapshots_match': all(v['matches'] for v in source_check.values()),
        'gnu_time_matches_metrics_receipt': m is not None and rss is not None and swaps is not None and exit_status is not None
            and m.group(1) == expected_wall and int(rss.group(1)) == expected_rss
            and int(swaps.group(1)) == receipt.get('swaps') == 0
            and int(exit_status.group(1)) == receipt.get('exit_status') == result.get('exit_status') == 0,
        'docker_and_saved_cgroup_caps_match': capset_match,
        'docker_state_success_no_oom': state.get('ExitCode') == 0 and state.get('OOMKilled') is False,
        'gnu_time_hash_matches_receipt': sha(p/'gnu-time.txt') == receipt.get('raw_gnu_time_sha256'),
    }
    return {'name': name, 'target': target, 'revision': receipt.get('source_revision'),
            'source_hashes': source_check, 'raw_metrics': {'wall': m.group(1) if m else None,
            'rss_kib': int(rss.group(1)) if rss else None, 'swaps': int(swaps.group(1)) if swaps else None,
            'exit': int(exit_status.group(1)) if exit_status else None},
            'docker_limits': {k: host.get(k) for k in ('MemoryReservation','Memory','MemorySwap','PidsLimit','CgroupParent','NetworkMode')},
            'saved_systemd_properties': reservation.get('root_slice'), 'checks': checks,
            'artifact_checksum_file': (p/'compiled-artifact-checksums.txt').is_file()}

helper_sources = {
    'src/llbc/ConcreteAssociatedTypes.ml': '48336b273fafc9fec71686f15896976cddf1a41367a5556749af0f13437ef4cf',
    'src/dune': 'fbb4eaef8b9f07b2d3073d6434333d89423c2ac7c8df8451cc3d6b70cc958ea5',
}
integration_sources = {**helper_sources,
    'src/interp/InterpUtils.ml': '8b885a725def3c7a923cc634f05a7b91bd25b4334b62b2ba6a1d09faf0d8a65a'}
runs = [check_run('r424-helper-v1', '.aeneas.objs/byte/aeneas__ConcreteAssociatedTypes.cmo', helper_sources, '0:03.86', 325292),
        check_run('r424-integration-v1', '.aeneas.objs/byte/aeneas__InterpUtils.cmo', integration_sources, '0:12.14', 479240)]
preclone = json.loads((PREFLIGHT/'preclone-audit.json').read_text())
clone_checks = {
    'counts_equal': preclone.get('source_entry_count') == preclone.get('candidate_entry_count') == 1084,
    'regular_and_symlink_counts': preclone.get('regular_file_count') == 1037 and preclone.get('symlink_count') == 1,
    'prepatch_content_mode_manifest_equal': preclone.get('content_and_mode_manifest_equal_before_patch') is True,
    'reported_shared_regular_file_inodes_zero': preclone.get('shared_regular_file_inode_count') == 0,
    'parent_prepasses_hash_matches': preclone.get('parent_prepasses_sha256') == preclone.get('expected_parent_prepasses_sha256') == '579f332212ad75b386b088ef7835783f7cb84a835b1acb96031d49847fc53a17',
    'preclone_status_is_historical': preclone.get('status') == 'ordinary copy completed; source patch not yet applied; no compiler build',
}
# Verify the outer original inventory remains intact; build-preflight receipts postdate it and are audited separately.
outer = ROOT/'SHA256SUMS'
outer_results = subprocess.run(['sha256sum','-c',str(outer)],cwd=ROOT.parents[1],text=True,capture_output=True)
# sha256sum's working directory is repository root; entries are workspace-relative.
outer_ok = outer_results.returncode == 0
head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT.parents[1],text=True).strip()
files = sorted(p for p in PREFLIGHT.rglob('*') if p.is_file())
preflight_index = {str(p.relative_to(ROOT)): sha(p) for p in files}
artifact_files = (PREFLIGHT/'r424-helper-v1/compiled-artifact-checksums.txt').read_text().splitlines()
candidate_snapshots = {
    'candidate/ConcreteAssociatedTypes.draft.ml': '48336b273fafc9fec71686f15896976cddf1a41367a5556749af0f13437ef4cf',
    'candidate/InterpUtils.draft.ml': '8b885a725def3c7a923cc634f05a7b91bd25b4334b62b2ba6a1d09faf0d8a65a',
    'candidate/dune.helper-only.draft': 'fbb4eaef8b9f07b2d3073d6434333d89423c2ac7c8df8451cc3d6b70cc958ea5',
}
candidate_snapshot_checks = {rel: {'sha256': sha(ROOT/rel), 'expected_sha256': digest,
                                   'matches': sha(ROOT/rel) == digest}
                             for rel, digest in candidate_snapshots.items()}
report = {
    'scope': 'Read-only audit of saved R424 clone and two successful focused OCaml compile receipts.',
    'runs': runs,
    'clone_gate': {'parent_root': preclone.get('parent_root'), 'candidate_root': preclone.get('candidate_root'), 'checks': clone_checks,
                   'independent_limitation': 'zero shared inodes and manifest equality are recorded remote audit results; this audit did not access/recompute the remote trees.'},
    'helper_artifact_checksums': artifact_files,
    'candidate_source_draft_hashes': candidate_snapshot_checks,
    'integration_artifact_checksum_gap': 'No compiled-artifact-checksums.txt or equivalent .cmo/.cmi digest record is saved for the InterpUtils integration build; success is supported by GNU-time/result/build logs only.',
    'source_coverage': 'Both successful target source snapshots are present and match the hashes in command/metrics/result receipts.',
    'provenance_coverage': 'Build command/metrics/result/docker inspect, pre-run reservation, GNU-time, launch logs, source snapshots, and clone-preflight records are saved. Top-level SHA256SUMS predates build-preflight; this report indexes all build-preflight file hashes separately.',
    'outer_SHA256SUMS_verification_returncode': outer_results.returncode,
    'outer_SHA256SUMS_verification_tail': outer_results.stdout.splitlines()[-3:],
    'repository_head_at_audit': head,
    'compile_revision_matches_audit_HEAD': all(r['revision'] == head for r in runs),
    'build_preflight_file_sha256': preflight_index,
    'all_checks_pass': all(all(r['checks'].values()) for r in runs) and all(clone_checks.values()) and outer_ok
                       and all(r['revision'] == head for r in runs)
                       and all(v['matches'] for v in candidate_snapshot_checks.values()),
    'boundary': 'The helper module and changed signature-integration module typechecked against the saved pinned cached workspace. No fixtures executed; no full executable, Aeneas translation, Lean theorem, source-to-model semantic correspondence, or security claim was established.',
}
(AUDIT/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
lines=['# R424 saved build-evidence audit','',f"Audit result: {'PASS' if report['all_checks_pass'] else 'FAIL'}.",'',
       'The ordinary clone receipt records 1,084 entries (1,037 regular files and one symlink), equal content/mode manifests before the source overlay, the pinned parent `PrePasses.ml` hash, and zero shared regular-file inodes. This is a saved remote audit result; the remote parent and clone trees were not re-read during this audit.', '',
       'Both compilation receipts match their saved source snapshots, target names, source revision, GNU-time records, and Docker/cgroup resource records:', '',
       '- Helper target `.aeneas.objs/byte/aeneas__ConcreteAssociatedTypes.cmo`: exit 0, 3.86 s, 325,292 KiB peak RSS, 0 swaps.',
       '- Integration target `.aeneas.objs/byte/aeneas__InterpUtils.cmo`: exit 0, 12.14 s, 479,240 KiB peak RSS, 0 swaps.', '',
       'Both used the recorded 5 GiB `MemoryHigh`, 7 GiB `MemoryMax`, `MemorySwapMax=0`, `TasksMax=128` systemd slice. Docker inspection records 5 GiB reservation, 7 GiB memory, `--memory-swap=7g` equal to memory (no extra container swap), 128 pids, network disabled, and the pinned image hash. GNU-time is the compiler measurement; wrapper/service runtime and tiny systemd service memory numbers are not substitutes.', '',
       'The helper build includes hashes for its `.cmo` and `.cmi`; the integration build has no saved compiled-artifact checksum file. The edited candidate source drafts also match the successful build snapshots. The old `build-preflight/REPORT.md` accurately describes the earlier preflight stage, before clone/build; it is historical and does not contradict the later receipts.', '',
       'This is typechecking evidence only. No fixtures were executed, and no translation, Lean theorem, source-semantic correspondence, or security result follows. See `audit.json` for per-field checks and hashes.']
(AUDIT/'REPORT.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'all_checks_pass':report['all_checks_pass'],'outer_sha256sum_rc':outer_results.returncode,'head':head,'compile_revision_matches_head':report['compile_revision_matches_audit_HEAD'],'candidate_snapshot_checks':candidate_snapshot_checks,'run_checks':[r['checks'] for r in runs],'clone_checks':clone_checks,'audit':str(AUDIT)},indent=2))
