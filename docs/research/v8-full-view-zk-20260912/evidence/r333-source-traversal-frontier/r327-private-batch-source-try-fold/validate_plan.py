#!/usr/bin/env python3
"""Static, offline validation of the unlaunched R327 extraction runner."""
from pathlib import Path
import ast, hashlib, json, re
root = Path(__file__).resolve().parent
runner = (root / 'run_extract.py').read_text()
base = Path(__file__).resolve().parents[1] / 'r297-private-norm-batch-monomorphized'
source = ast.parse(runner)
remote = next(ast.literal_eval(n.value) for n in source.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'REMOTE_SCRIPT' for t in n.targets))
assert 'R327_ALLOW_LAUNCH' in runner and 'unlaunched preparation' in runner
assert 'aspis-r327-private-batch-source-try-fold-20261002-a' in runner
assert 'aspisr327.slice' in runner
assert 'rustup\',\'run\',\'stable' not in runner
assert 'toolchain-version' in runner and 'toolchain-path' in runner and 'charon-driver' in runner
assert 'rustup\',\'run\',channel' in runner
assert runner.count("'--monomorphize'") == 1
patterns = [
    'core::iter::traits::iterator::Iterator::try_fold',
    'core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::branch',
    'core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::from_output',
    'core::ops::control_flow::{impl core::ops::try_trait::FromResidual<core::ops::control_flow::ControlFlow<_,core::convert::Infallible>> for core::ops::control_flow::ControlFlow<_,_>}::from_residual',
]
assert all(runner.count(p) == 3 for p in patterns), [(p, runner.count(p)) for p in patterns] # command, audit metadata, result metadata
oldcmd = json.loads((base/'extract-command.json').read_text())
old_includes = oldcmd['include']
for p in old_includes:
    assert runner.count("'" + p + "'") >= 3, (p, runner.count("'"+p+"'"))
# Substitute only the template tokens to parse the command-bearing remote script; no execution occurs.
r266 = json.loads((Path(__file__).resolve().parents[1]/'r266-private-inverse-leaf-extract'/'extract-command.json').read_text())
mapping = {
    '@ROOT0@': repr(oldcmd['start_from'][0]),
    '@START_JSON@': json.dumps(oldcmd['start_from']),
    '@SOURCE_ROOT@': '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a',
    '@REMOTE_ROOT@': '/home/dombarker/project-offloads/aspis-r327-private-batch-source-try-fold-20261002-a',
    '@CIRCLE_HASH@': oldcmd['verified_source_hashes']['circle_norm.rs'],
    '@LINE_HASH@': oldcmd['verified_source_hashes']['line_norm.rs'],
    '@JOINED_HASH@': oldcmd['verified_source_hashes']['joined_inverse.rs'],
    '@FIELD_HASH@': oldcmd['verified_source_hashes']['aspis_core_field.rs'],
    '@MANIFEST_HASH@': oldcmd['verified_source_hashes']['performance_host_Cargo.toml'],
    '@LOCK_HASH@': oldcmd['verified_source_hashes']['performance_host_Cargo.lock'],
    '@SOURCE_REVISION@': 'DYNAMIC_GIT_REV_AT_RUN',
    '@RUSTFLAGS_HASH@': r266['rustflags_sha256'],
    '@EXPECTED_RUSTFLAGS@': repr(r266['rustflags']),
}
for key, value in mapping.items():
    remote = remote.replace(key, value)
compile(remote, '<R327_REMOTE_SCRIPT>', 'exec')
inner = ast.parse(remote)
cmd_node = next(n.value for n in inner.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'cmd' for t in n.targets))
assert isinstance(cmd_node, ast.List)
args = [x.value for x in cmd_node.elts if isinstance(x, ast.Constant) and isinstance(x.value, str)]
includes = [args[i+1] for i, a in enumerate(args[:-1]) if a == '--include']
assert includes == old_includes + patterns, (includes, old_includes + patterns)
for option in ('--monomorphize', '--sysroot', 'default', '--offline', '--locked', '--release', '--jobs', '1'):
    assert option in args, option
assert 'insecure-spend-fixture,selected-v7-kernels' in args
# Existing non-include command options are preserved relative to R297.
assert oldcmd['start_from'] == ['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch']
plan = {
    'status': 'prepared_unlaunched',
    'runner': 'run_extract.py',
    'runner_sha256': hashlib.sha256((root/'run_extract.py').read_bytes()).hexdigest(),
    'remote_script_sha256_after_static_substitution': hashlib.sha256(remote.encode()).hexdigest(),
    'static_validation': 'python syntax and embedded remote-script syntax parsed; command AST verified; no runner import, SSH, systemd, Cargo, Charon extraction, or Lean execution performed',
    'prep_worktree_head': '469bdd2cdd73f88385114074e27e1f9e566c3022',
    'launch_revision_behavior': 'runner dynamically calls git rev-parse HEAD at actual launch and stores that revision; frozen remote source snapshot has no Git metadata',
    'remote_root': '/home/dombarker/project-offloads/aspis-r327-private-batch-source-try-fold-20261002-a',
    'source_revision_source_root': '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a',
    'charon_sha256': 'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c',
    'toolchain_receipt': 'runner records charon version, embedded channel, selected sysroot, selected nightly rustc/cargo versions, charon/driver hashes and resolved rustc_driver library hash',
    'start_from': oldcmd['start_from'],
    'added_include_patterns': patterns,
    'retained_prior_includes': old_includes,
    'monomorphize': True,
    'preserved_cargo_args': ['--offline', '--locked', '--release', '--jobs', '1', '--features', 'insecure-spend-fixture,selected-v7-kernels', '--bin', 'aspis-v8-performance-host'],
    'rustflags_sha256': r266['rustflags_sha256'],
    'source_hashes': oldcmd['verified_source_hashes'],
    'resource_cap': {'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128,'new_named_system_slice':'aspisr327.slice','new_user_service':'aspis-r327-private-batch-source-try-fold'},
    'expected_work': 'focused cached release-source extraction; not benchmarks or arithmetic release gates',
    'nonclaims': ['no extraction result exists yet', 'candidate include selection is not validated by a Charon run', 'no claim that additional includes produce a body in monomorphized translation']
}
(root/'launch-plan.json').write_text(json.dumps(plan, indent=2)+'\n')
print('R327 plan syntax and exact include/option checks passed; status remains prepared_unlaunched.')
