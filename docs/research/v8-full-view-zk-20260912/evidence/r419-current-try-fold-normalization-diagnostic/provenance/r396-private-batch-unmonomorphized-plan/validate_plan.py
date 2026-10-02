#!/usr/bin/env python3
"""Static validation of the exact R396 extraction delta; never launches tools."""
from pathlib import Path
import ast, hashlib, json
root=Path(__file__).resolve().parent
runner=(root/'run_extract.py').read_text()
r327=Path(__file__).resolve().parents[1]/'r327-private-batch-source-try-fold'
old=json.loads((r327/'extract-command.json').read_text())
r266=json.loads((Path(__file__).resolve().parents[1]/'r266-private-inverse-leaf-extract'/'extract-command.json').read_text())
assert 'R396_ALLOW_LAUNCH' in runner and 'unlaunched preparation' in runner
assert 'aspis-r396-private-batch-unmonomorphized-20261002-a' in runner
assert '--unit=aspis-r396-private-batch-unmonomorphized' in runner
assert 'aspisr396.slice' in runner
assert "'--monomorphize'" not in runner
assert "'monomorphize':False" in runner
assert 'MemoryHigh=5G' in runner and 'MemoryMax=7G' in runner and 'MemorySwapMax=0' in runner and 'TasksMax=128' in runner
assert 'aggregate_reservation_gate' in runner and 'candidate_memory_max_bytes' in runner
assert 'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c' in runner
assert "channel == 'nightly-2026-06-01'" in runner and '14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' in runner
assert runner.count('SOURCE_HASHES') >= 2
assert "'--offline'" in runner and "'--locked'" in runner and "'--release'" in runner and "'--jobs','1'" in runner
src=ast.parse(runner)
remote=next(ast.literal_eval(n.value) for n in src.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='REMOTE_SCRIPT' for t in n.targets))
mapv={
'@ROOT0@':repr(old['start_from'][0]), '@START_JSON@':json.dumps(old['start_from']),
'@SOURCE_ROOT@':'/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a',
'@REMOTE_ROOT@':'/home/dombarker/project-offloads/aspis-r396-private-batch-unmonomorphized-20261002-a',
'@CIRCLE_HASH@':old['verified_source_hashes']['circle_norm.rs'], '@LINE_HASH@':old['verified_source_hashes']['line_norm.rs'],
'@JOINED_HASH@':old['verified_source_hashes']['joined_inverse.rs'], '@FIELD_HASH@':old['verified_source_hashes']['aspis_core_field.rs'],
'@MANIFEST_HASH@':old['verified_source_hashes']['performance_host_Cargo.toml'], '@LOCK_HASH@':old['verified_source_hashes']['performance_host_Cargo.lock'],
'@SOURCE_REVISION@':'DYNAMIC_GIT_REV_AT_RUN', '@RUSTFLAGS_HASH@':r266['rustflags_sha256'], '@EXPECTED_RUSTFLAGS@':repr(r266['rustflags'])}
for k,v in mapv.items(): remote=remote.replace(k,v)
compile(remote,'<R396_REMOTE_SCRIPT>','exec')
inner=ast.parse(remote)
cmdnode=next(n.value for n in inner.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='cmd' for t in n.targets))
assert isinstance(cmdnode,ast.List)
args=[ast.literal_eval(x) if isinstance(x,ast.Constant) else None for x in cmdnode.elts]
assert '--monomorphize' not in args
destpos=args.index('--dest-file')+1
assert isinstance(cmdnode.elts[destpos],ast.Call) and ast.unparse(cmdnode.elts[destpos]) == "str(root / 'R396PrivateBatchUnmonomorphized.llbc')"
args[destpos]='/home/dombarker/project-offloads/aspis-r396-private-batch-unmonomorphized-20261002-a/R396PrivateBatchUnmonomorphized.llbc'
args[0]='/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon'
manifestpos=args.index('--manifest-path')+1
assert ast.unparse(cmdnode.elts[manifestpos]) == 'str(manifest)'
args[manifestpos]='/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a/docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'
oldargs=old['command']
# Charon command exact token comparison after removing the one mono flag and substituting only fresh dest path.
expected=[x for x in oldargs if x!='--monomorphize']
expected[expected.index('--dest-file')+1]='/home/dombarker/project-offloads/aspis-r396-private-batch-unmonomorphized-20261002-a/R396PrivateBatchUnmonomorphized.llbc'
assert args==expected,(args,expected)
assert old['start_from']==['crate::circle_norm::joined_inverse::line_norm::r110_norm::batch']
assert 'core::iter::traits::iterator::Iterator::try_fold' in old['include']
assert all(p in old['include'] for p in ('core::option','aspis_core::field','core::slice::_::last'))
print('R396 static plan validation passed: inner command equals R327 command with only --monomorphize removed and fresh output path; caps, toolchain, and reservation gate present. No runner, SSH, systemd, Cargo, Charon, or Lean execution.')
