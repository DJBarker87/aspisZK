import hashlib, json, pathlib, re
root = pathlib.Path('.r21-scratch/r426-mutable-borrow-copy-frontier')
out = root / 'documentation-inventory'
plan = root / 'mir-diagnostic-plan'
res = json.loads((plan / 'result.json').read_text())
launch = json.loads((plan / 'launch.json').read_text())
cmd = json.loads((plan / 'extract-command.json').read_text())
aeneas = json.loads((root / 'aeneas/inventory.json').read_text())
api = json.loads((root / 'aeneas/normalization-api/inventory.json').read_text())
api_hashes_text = (root / 'aeneas/normalization-api/source-hashes.txt').read_text()
api_hashes = dict(re.findall(r'^\s*(\S+\.(?:ml|rs)) SHA256 ([0-9a-f]{64})$', api_hashes_text, re.M))
launch_plan = json.loads((plan / 'launch-plan.json').read_text())
gnu = (plan / 'gnu-time.txt').read_text()
def match(pattern):
 m = re.search(pattern, gnu, re.M)
 return m.group(1).strip() if m else None
metrics = {
 'wall_time': match(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)'),
 'peak_rss_kib': int(match(r'Maximum resident set size \(kbytes\):\s*(\d+)')),
 'swaps': int(match(r'Swaps:\s*(\d+)')),
 'gnu_time_exit_status': int(match(r'Exit status:\s*(\d+)')),
}
def artifact(path):
 p = pathlib.Path(path)
 return {'path': p.as_posix(), 'exists': p.is_file(), 'bytes': p.stat().st_size if p.is_file() else None, 'sha256': hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None}
primary_paths = [
 plan/'result.json',plan/'extract-command.json',plan/'gnu-time.txt',plan/'extract.log',plan/'charon.stderr.log',plan/'original-ullbc.stdout',plan/'R426OriginalUllbc.llbc',plan/'launch.json',plan/'host-reservation-before.json',plan/'host-reservation-after.json',plan/'toolchain.txt',plan/'run_original_ullbc.reviewed.py',plan/'manifest.json',plan/'launch-plan.json',plan/'README.md',plan/'SHA256SUMS',
 root/'llbc/copy-frontier-report.json',root/'llbc/R425-result.json',root/'llbc/R425-translate-command.json',root/'llbc/R425-translate.log',root/'llbc/R396-extract-command.json',root/'llbc/R396-extract.log',root/'llbc/R419-selected-functions.json',root/'aeneas/inventory.json',root/'aeneas/source-excerpts.txt',root/'aeneas/charon-excerpts.txt',root/'aeneas/rustc-mir-excerpts.txt',root/'aeneas/normalization-api/inventory.json',root/'aeneas/normalization-api/source-hashes.txt',root/'provenance-inventory/inventory.json',root/'provenance-inventory/README.md',root/'provenance-inventory/SHA256SUMS',root/'root-call-inventory/root-calls.json',root/'root-call-inventory/README.md',root/'root-call-inventory/SHA256SUMS']
external_paths = [
 '.r21-scratch/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc','.r21-scratch/r396-private-batch-unmonomorphized-plan/extract-command.json','.r21-scratch/r396-private-batch-unmonomorphized-plan/result.json','.r21-scratch/r396-private-batch-unmonomorphized-plan/source-body-audit.json','.r21-scratch/r396-private-batch-unmonomorphized-plan/selected-try-fold-row.json','.r21-scratch/r396-private-batch-unmonomorphized-plan/selected-try-fold-callees.json','.r21-scratch/r419-try-fold-equality-elimination/runs/aspis-r419-candidate-1790967913444473000/candidate.llbc','.r21-scratch/r425-unit-constant-frontier/translation-runner/output/ee7ba72da456-20261002T210856Z/metrics-receipt.json','.r21-scratch/r425-unit-constant-frontier/translation-runner/output/ee7ba72da456-20261002T210856Z/translate.log','docs/research/v8-full-view-zk-20260912/evidence/r333-source-traversal-frontier/r323-charon-compiler-provenance/nightly-rust-source/iterator.rs','docs/research/v8-full-view-zk-20260912/evidence/r333-source-traversal-frontier/r323-charon-compiler-provenance/pinned-charon/driver.rs']
source_hashes = {k:{'before':v,'after':res['source_hashes_after'][k],'same':v==res['source_hashes_after'][k]} for k,v in sorted(res['source_hashes_before'].items())}
info = {
 'task':'R426 saved-evidence documentation inventory; scratch only. No build, extraction, translation, or comparison rerun.',
 'finite_boundary':{
  'result':'One saved Charon --print-original-ullbc command completed exit 0 and emitted original-ULLBC stdout plus serialized LLBC. This is Charon ULLBC after MIR translation and before Charon cleanup passes, not raw rustc MIR.',
  'metrics':metrics,'source_revision_recorded':res['source_revision_recorded'],'resource_caps':launch['caps'],'systemd_unit':'aspis-r426-original-ullbc','formal_axioms':'N/A; no Lean target was generated or compiled.'},
 'capture':{
  'source_root':launch['remote_source_root'],'output_root':launch['remote_output_root'],'exact_command_file':'mir-diagnostic-plan/extract-command.json','exact_charon_argv':cmd['command'],'source_hashes_before_after':source_hashes,
  'rustflags_sha256':cmd['rustflags_sha256'],'charon_sha256':launch_plan['charon_sha256'],'rustc_channel':launch_plan['rust_channel'],'rustc_commit':launch_plan['rustc_commit'],
  'serialized_llbc_sha256':res['llbc_sha256'],'original_ullbc_stdout_sha256':res['original_ullbc_stdout_sha256'],'original_ullbc_stdout_bytes':res['original_ullbc_stdout_bytes']},
 'initial_comparison_gate':{
  'compared':res['baseline_comparison']['compared'],'equal_after_operational_option_normalization':res['baseline_comparison']['equal_after_operational_option_normalization'],
  'R396_baseline_sha256_before_after':[res['R396_baseline_sha256_before'],res['R396_baseline_sha256_after']],
  'assertion':'The saved initial exact-serialized comparison gate failed; raw comparison and launch output are preserved. The Charon child exited 0, while the launch wrapper exited 1 on its comparison assertion. This inventory does not finalize equivalence or resolve short_names ordering.'},
 'prior_translation_failure':{'input_llbc_sha256':'7f82eaabe855e89d735b21f9af5f6a983abea6b2f4d93d4b8bae747abd2829e2','exit_status':2,'wall_time_seconds':0.77,'peak_rss_kib':142032,'swaps':0,'no_Lean_output':True,'diagnostic':'Aeneas rejected a mutable-borrow Copy at InterpExpressions.ml:234 for the Iterator::next call span; raw R425 log/receipt preserved.'},
 'first_missing_provenance':{'proposition':'Identify the exact selected Rust frontend MIR receiver/lowering ancestry for try_fold self.next(), including any temporary reborrow, CopyForDeref, and Retag facts, and how Charon translates that exact MIR occurrence.','observed':'R396/R419 LLBC records Copy(Local 1) typed &mut Self at iterator.rs:2493:28-39; the captured pre-micropass ULLBC prints copy self. Pinned Charon source preserves MIR Copy/Move categories. No saved raw MIR statement or query trace links this occurrence to a MIR predecessor or Retag.','limit':'Pinned compiler documentation and generic lowering paths are context only; they do not attribute a specific lowering to this operand.'},
 'historical_preflight_snapshots':[{'path':f'mir-diagnostic-plan/{n}','sha256':artifact(plan/n)['sha256'],'status':'pre-launch planning snapshot, retained unchanged and superseded for execution outcome'} for n in ['README.md','manifest.json','launch-plan.json']],
 'source_tool_pins':{'selected_rust_files':source_hashes,'pinned_aeneas_files':aeneas['pinned_aeneas_source_sha256'],'pinned_charon_files':aeneas['pinned_charon']['source_sha256'],'pinned_rustc_files':api_hashes,'rustc_source_context':api['rustc_source'],'source_call_inventory':'root-call-inventory/root-calls.json (AST/source facts only)'},
 'authoritative_files':[artifact(p) for p in primary_paths],
 'referenced_inputs_and_pins':[artifact(p) for p in external_paths],
 'scope_exclusions':['No unrelated scratch directories are copied into this inventory.','No tracked research documentation is modified.','No equality, source-semantics, or proof conclusion is made.']
}
(out/'inventory.json').write_text(json.dumps(info,indent=2)+'\n')
