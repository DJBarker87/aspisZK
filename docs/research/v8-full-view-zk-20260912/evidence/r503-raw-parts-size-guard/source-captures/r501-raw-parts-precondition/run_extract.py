#!/usr/bin/env python3
"""R501: capture the raw-parts precondition dependency selected from R495 LLBC."""
import hashlib
import json
import pathlib
import shlex
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
WORKTREE = HERE.parents[1]
R494 = WORKTREE / "docs/research/v8-full-view-zk-20260912/evidence/r490-align-offsets-source/r494-result.json"
record = json.loads(R494.read_text())
HOST = "dombarker@100.108.41.90"
SSH = ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
SCP = ["scp", "-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
SOURCE = "/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a"
REMOTE = "/home/dombarker/project-offloads/aspis-r501-raw-parts-precondition-20261003-a"
CHARON = "/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon"
INCLUDES = [
    "core::option", "core::result::_::map_err", "aspis_core::field",
    "core::slice::_::align_to", "core::slice::_::align_to_offsets",
    "core::mem::SizedTypeProperties::SIZE", "core::mem::SizedTypeProperties::ALIGN",
    "core::mem::SizedTypeProperties::IS_ZST", "core::slice::_::chunks_exact",
    "core::slice::iter::_::next", "core::slice::_::split_at_unchecked",
    "core::num::_::unchecked_sub::precondition_check",
    "core::slice::raw::from_raw_parts::precondition_check",
]
assert record["source_revision"] == "4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35"
assert record["retry2_RUSTFLAGS_sha256"] == hashlib.sha256(json.dumps(shlex.split(record["retry2_RUSTFLAGS_text"]), separators=(",", ":")).encode()).hexdigest()

REMOTE_SCRIPT = r'''import hashlib,json,os,pathlib,shlex,subprocess,sys
source=pathlib.Path(@SOURCE@)
root=pathlib.Path(@REMOTE@)
charon=pathlib.Path(@CHARON@)
expected_hashes=@HASHES@
paths={
 "r110_norm.rs":source/'docs/research/v8-no-work-100-20260907/experiments/r110_norm.rs',
 "circle_norm.rs":source/'docs/research/v8-no-work-100-20260907/experiments/circle_norm.rs',
 "line_norm.rs":source/'docs/research/v8-no-work-100-20260907/experiments/line_norm.rs',
 "joined_inverse.rs":source/'docs/research/v8-no-work-100-20260907/experiments/joined_inverse.rs',
 "aspis_core_field.rs":source/'crates/aspis-core/src/field.rs',
 "performance_host_Cargo.toml":source/'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml',
 "performance_host_Cargo.lock":source/'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.lock',
 "relation_callback.rs":source/'docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs',
 "r105_parse.rs":source/'docs/research/v8-no-work-100-20260907/experiments/r105_parse.rs'}
actual={k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in paths.items()}
assert actual==expected_hashes,(actual,expected_hashes)
assert not root.exists(), root
root.mkdir(parents=True)
workspace=paths['performance_host_Cargo.toml'].parent
fingerprints=list((workspace/'target/x86_64-unknown-linux-gnu/release/.fingerprint').glob('aspis-v8-performance-host*/bin-aspis-v8-performance-host.json'))
flags=[json.loads(p.read_text())['rustflags'] for p in fingerprints]
assert flags and all(f==flags[0] for f in flags)
expected_flags=@RUSTFLAGS@
assert shlex.join(flags[0])==expected_flags
flag_text=shlex.join(flags[0])
os.environ['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:'+os.environ.get('PATH','')
os.environ['RUSTFLAGS']=flag_text
assert hashlib.sha256(json.dumps(flags[0],separators=(',',':')).encode()).hexdigest()==@RUSTFLAGS_SHA@
assert hashlib.sha256(charon.read_bytes()).hexdigest()==@CHARON_SHA@
cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--monomorphize','--consts','values','--sysroot','default','--start-from','crate::r105_parse::fields']
for i in @INCLUDES@: cmd += ['--include',i]
cmd += ['--dest-file',str(root/'R501RawPartsPrecondition.llbc'),'--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',str(paths['performance_host_Cargo.toml']),'--bin','aspis-v8-performance-host']
# Prevent this 7-GiB cap from exceeding the 40-GiB concurrent reservation.
names=[x.split()[0] for x in subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True).splitlines() if x.split()]
def limit(name):
 out=subprocess.check_output(['systemctl','--user','show',name,'-p','MemoryMax'],text=True).strip().split('=',1)[-1]
 try: return int(out)
 except ValueError: return 0
active_limits={n:limit(n) for n in names}
assert sum(active_limits.values())+7*1024**3 <= 40*1024**3,active_limits
before={'source_hashes':actual,'source_revision':@REV@,'rustflags_sha256':hashlib.sha256(json.dumps(flags[0],separators=(',',':')).encode()).hexdigest(),'charon_sha256':hashlib.sha256(charon.read_bytes()).hexdigest(),'argv':cmd,'active_service_memory_max':active_limits,'new_scope_memory_max':7*1024**3,'aggregate_limit_max':40*1024**3,'meminfo':pathlib.Path('/proc/meminfo').read_text(),'toolchain_version':subprocess.check_output([str(charon),'toolchain-version'],text=True).strip(),'toolchain_path':subprocess.check_output([str(charon),'toolchain-path'],text=True).strip()}
(root/'capture-command.json').write_text(json.dumps(before,indent=2)+'\n')
with (root/'charon.stdout.log').open('w') as out, (root/'charon.stderr.log').open('w') as err:
 run=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=out,stderr=err)
llbc=root/'R501RawPartsPrecondition.llbc'
result={'target':'R501 raw-parts precondition LLBC capture','source_revision':@REV@,'source_hashes':actual,'charon_exit_status':run.returncode,'llbc_exists':llbc.is_file(),'rustflags_sha256':hashlib.sha256(json.dumps(flags[0],separators=(',',':')).encode()).hexdigest(),'charon_sha256':hashlib.sha256(charon.read_bytes()).hexdigest(),'includes':@INCLUDES@,'measurement_source':'/usr/bin/time -v in charon.stderr.log','formal_axioms':'N/A; LLBC capture only'}
if llbc.is_file():
 result['llbc_sha256']=hashlib.sha256(llbc.read_bytes()).hexdigest();result['llbc_bytes']=llbc.stat().st_size
 try:
  data=json.loads(llbc.read_text());result['has_errors']=data.get('has_errors')
 except Exception as e: result['llbc_json_error']=str(e)
(root/'result.json').write_text(json.dumps(result,indent=2)+'\n')
sys.exit(run.returncode)
'''

def q(x): return repr(x)
remote = REMOTE_SCRIPT.replace("@SOURCE@", q(SOURCE)).replace("@REMOTE@", q(REMOTE)).replace("@CHARON@", q(CHARON))
remote = remote.replace("@HASHES@", repr(record["source_hashes"])).replace("@RUSTFLAGS@", q(record["retry2_RUSTFLAGS_text"]))
remote = remote.replace("@RUSTFLAGS_SHA@", q(record["retry2_RUSTFLAGS_sha256"])).replace("@CHARON_SHA@", q("b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c"))
remote = remote.replace("@INCLUDES@", repr(INCLUDES)).replace("@REV@", q(record["source_revision"]))
unit = "aspis-r501-raw-parts-precondition-20261003"
systemd = ["systemd-run", "--user", "--wait", "--collect", "--pipe", f"--unit={unit}", f"--working-directory={SOURCE}", "-p", "MemoryHigh=5G", "-p", "MemoryMax=7G", "-p", "MemorySwapMax=0", "-p", "TasksMax=128", "python3", "-c", remote]
ssh_cmd = [*SSH, HOST, shlex.join(systemd)]
(HERE / "launch.json").write_text(json.dumps({"target":"R501 raw-parts precondition LLBC capture", "source_revision":record["source_revision"], "remote_root":REMOTE, "systemd_argv":systemd, "ssh_argv":ssh_cmd, "source_hashes":record["source_hashes"], "includes":INCLUDES, "caps":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128}}, indent=2)+"\n")
with (HERE / "ssh-output.log").open("w") as log:
    launch = subprocess.run(ssh_cmd, stdout=log, stderr=subprocess.STDOUT)
for name in ("capture-command.json", "charon.stdout.log", "charon.stderr.log", "result.json", "R501RawPartsPrecondition.llbc"):
    copy = subprocess.run([*SCP, f"{HOST}:{REMOTE}/{name}", str(HERE / name)])
    if copy.returncode and name != "R501RawPartsPrecondition.llbc":
        sys.exit(copy.returncode)
sys.exit(launch.returncode)
