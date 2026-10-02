#!/usr/bin/env python3
"""Run the lead-specified bounded R207 Charon extraction on the NUC."""
import hashlib
import json
import pathlib
import shlex
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
WORKTREE = HERE.parents[1]
R185_COMMAND = WORKTREE / ".r21-scratch/r185-monomorphic-freeze/extract-command.json"
expected = json.loads(R185_COMMAND.read_text())["rustflags"]
source_sha = "4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f"
source_revision = "237d48bc3f70c262a27e9a8595b9ac51d12b4e77"

remote_script = f'''import os,pathlib,hashlib,subprocess,json,shlex
hostroot=pathlib.Path('/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a')
source=hostroot/'docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs'
assert hashlib.sha256(source.read_bytes()).hexdigest()=={source_sha!r}
root=pathlib.Path('/home/dombarker/project-offloads/aspis-r207-vector-copy-extract-20261002-a')
assert not root.exists(), f'output already exists: {{root}}'
root.mkdir()
os.environ['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:'+os.environ.get('PATH','')
workspace=hostroot/'docs/research/v8-no-work-100-20260907/experiments/performance-host'
fingerprints=list((workspace/'target/x86_64-unknown-linux-gnu/release/.fingerprint').glob('aspis-v8-performance-host*/bin-aspis-v8-performance-host.json'))
flags=[json.loads(p.read_text())['rustflags'] for p in fingerprints]
assert flags and all(x==flags[0] for x in flags)
assert flags[0]=={expected!r}
os.environ['RUSTFLAGS']=shlex.join(flags[0])
manifest=workspace/'Cargo.toml'
charon='/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon'
cmd=[charon,'cargo','--preset','aeneas','--mir','built','--monomorphize','--sysroot','default','--start-from','crate::freeze','--include','core::option','--include','core::result::_::map_err','--include','aspis_core::field','--include','aspis_core::circle','--include','aspis_core::transcript','--include','alloc::vec::_::extend','--include','alloc::vec::_::into_iter','--include','alloc::vec::spec_extend::_::spec_extend','--include','alloc::vec::into_iter::_::as_slice','--include','alloc::vec::_::append_elements','--dest-file',str(root/'R207VectorCopy.llbc'),'--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',str(manifest),'--bin','aspis-v8-performance-host']
(root/'extract-command.json').write_text(json.dumps({{'command':cmd,'rustflags':flags[0],'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'source_revision':{source_revision!r},'expected_cost':'cached optimized release host build and bounded Charon extraction'}},indent=2))
with (root/'extract.log').open('w') as f:
 r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
print((root/'extract.log').read_text()[-5000:]);print('EXTRACT_EXIT',r.returncode)
raise SystemExit(r.returncode)
'''

ssh_opts = ["-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
host = "dombarker@100.108.41.90"
remote_cmd = [
    "systemd-run", "--user", "--wait", "--collect", "--pipe",
    "--unit=aspis-r207-vector-copy-extract",
    "--working-directory=/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a",
    "-p", "MemoryHigh=5G", "-p", "MemoryMax=7G", "-p", "MemorySwapMax=0", "-p", "TasksMax=128",
    "python3", "-c", remote_script,
]
local_command = ["ssh", *ssh_opts, host, shlex.join(remote_cmd)]
(HERE / "launch.json").write_text(json.dumps({
    "local_runner": str(pathlib.Path(__file__).resolve()),
    "local_runner_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
    "source_sha256_asserted": source_sha,
    "source_revision_recorded": source_revision,
    "rustflags_expected_from_r185": expected,
    "ssh_argv": local_command,
    "systemd_argv": remote_cmd,
    "caps": {"MemoryHigh": "5G", "MemoryMax": "7G", "MemorySwapMax": "0", "TasksMax": 128},
}, indent=2) + "\n")
with (HERE / "ssh-output.log").open("w") as out:
    result = subprocess.run(local_command, stdout=out, stderr=subprocess.STDOUT)
print((HERE / "ssh-output.log").read_text())

remote_root = "/home/dombarker/project-offloads/aspis-r207-vector-copy-extract-20261002-a"
for name in ("extract-command.json", "extract.log", "R207VectorCopy.llbc"):
    scp_cmd = ["scp", *ssh_opts, f"{host}:{remote_root}/{name}", str(HERE / name)]
    copied = subprocess.run(scp_cmd)
    if copied.returncode and name != "R204VectorExtend.llbc":
        sys.exit(copied.returncode)
sys.exit(result.returncode)
