#!/usr/bin/env python3
"""R569 target-only frozen masked-claim Charon capture; no translation."""
import hashlib, json, pathlib, shlex, subprocess

HERE = pathlib.Path(__file__).resolve().parent
WORKTREE = HERE.parents[1]
HOST = "dombarker@100.108.41.90"
SSH = ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
SCP = ["scp", "-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
SOURCE = "/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a"
STAGE = "/home/dombarker/project-offloads/aspis-r569-masked-claim-20261004-a"
CHARON = "/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon"
CHARON_SHA = "b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c"
STATE_SHA = "18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f"
RUSTFLAGS = (WORKTREE / "docs/research/v8-full-view-zk-20260912/evidence/r555-zero-output-rejoin/selected-rustflags.txt").read_text().strip()
RUSTFLAGS_SHA_FILE = hashlib.sha256((WORKTREE / "docs/research/v8-full-view-zk-20260912/evidence/r555-zero-output-rejoin/selected-rustflags.txt").read_bytes()).hexdigest()
assert RUSTFLAGS_SHA_FILE == "df02f7fe2415264263ea8dca33d686314b1c06ef27bf4d039df9e587513d28b8"
assert hashlib.sha256(json.dumps(shlex.split(RUSTFLAGS), separators=(",", ":")).encode()).hexdigest() == "f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613"

REMOTE_SCRIPT = r'''import hashlib,json,os,pathlib,shutil,subprocess,sys
source=pathlib.Path(@SOURCE@); stage=pathlib.Path(@STAGE@); charon=pathlib.Path(@CHARON@)
assert not stage.exists(),stage
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def tree(root): return {str(p.relative_to(root)):sha(p) for p in sorted(root.rglob('*')) if p.is_file()}
ignore=shutil.ignore_patterns('target','.git','.lake','node_modules','.pytest_cache')
shutil.copytree(source,stage,ignore=ignore)
src_core=source/'crates/aspis-core'; dst_core=stage/'crates/aspis-core'
core_src=tree(src_core/'src'); core_dst=tree(dst_core/'src')
assert core_src==core_dst,(len(core_src),len(core_dst))
assert sha(src_core/'build.rs')==sha(dst_core/'build.rs')
assert sha(src_core/'Cargo.toml')==sha(dst_core/'Cargo.toml')
assert core_src['src/state_only_hiding.rs']==@STATE_SHA@
assert sha(source/'Cargo.lock')==sha(stage/'Cargo.lock')
host_rel=pathlib.Path('docs/research/v8-no-work-100-20260907/experiments')
host_src=source/host_rel; host_dst=stage/host_rel
for name in ['relation_callback.rs','performance-host/Cargo.toml','performance-host/Cargo.lock']:
 assert sha(host_src/name)==sha(host_dst/name),name
orig_cb=host_dst/'relation_callback.rs'; orig_sha=sha(orig_cb)
probe="\n\n// R569 capture-only root. This is the sole source delta in the isolated stage.\npub fn claim_probe(\n    transcript: &mut corelib::transcript::Transcript,\n    claim: corelib::field::QM31,\n) -> Result<corelib::field::QM31, corelib::state_only_hiding::StateOnlyHidingScheduleError> {\n    corelib::state_only_hiding::begin_state_only_masked_sumcheck(transcript, claim)\n}\n"
with orig_cb.open('ab') as f: f.write(probe.encode())
actual=sha(charon); assert actual==@CHARON_SHA@
manifest=host_dst/'performance-host/Cargo.toml'
cargo=json.loads('null') if False else manifest.read_text()
assert 'selected-v7-kernels' in cargo and 'insecure-spend-fixture' in cargo
assert sha(host_dst/'performance-host/Cargo.lock')==sha(host_src/'performance-host/Cargo.lock')
flags=@RUSTFLAGS@
env=os.environ.copy(); env.update({'PATH':'/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':flags,'CARGO_TARGET_DIR':str(host_src/'performance-host/target')})
cmd=[str(charon),'cargo','--preset','aeneas','--mir','built','--monomorphize','--consts','values','--sysroot','default','--start-from','crate::claim_probe']
includes=['core::option','core::result::_::map_err','aspis_core::state_only_hiding::begin_state_only_masked_sumcheck','aspis_core::transcript','aspis_core::field']
for i in includes: cmd += ['--include',i]
llbc=stage/'R569MaskedClaim.llbc'
cmd += ['--dest-file',str(llbc),'--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',str(manifest),'--bin','aspis-v8-performance-host']
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True)
reservations=[]
for line in units.splitlines():
 parts=line.split()
 if not parts or not parts[0].startswith('aspis'): continue
 val=subprocess.check_output(['systemctl','--user','show',parts[0],'-p','MemoryMax'],text=True).strip().split('=',1)[1]
 if val.isdigit(): reservations.append((parts[0],int(val)))
assert sum(v for _,v in reservations)+7*1024**3<=40*1024**3,reservations
before={'target':'R569 target-only actual masked claim function Charon capture','source_revision':'4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35','source_freeze_revision':'6677d5f1310ff7373301fbd79f186278f772e68a','launch_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=source,text=True).strip() if (source/'.git').exists() else 'no .git metadata in pinned frozen source root','source_root':str(source),'stage_root':str(stage),'source_core_src_files':core_src,'source_core_build_sha256':sha(src_core/'build.rs'),'source_core_cargo_sha256':sha(src_core/'Cargo.toml'),'source_cargo_lock_sha256':sha(source/'Cargo.lock'),'host_cargo_sha256':sha(host_src/'performance-host/Cargo.toml'),'host_lock_sha256':sha(host_src/'performance-host/Cargo.lock'),'host_relation_callback_original_sha256':orig_sha,'stage_host_relation_callback_with_single_probe_sha256':sha(orig_cb),'probe_source_delta':probe,'rustflags':flags,'rustflags_file_sha256':@RUSTFLAGS_FILE_SHA@,'rustflags_normalized_sha256':hashlib.sha256(json.dumps(__import__('shlex').split(flags),separators=(',',':')).encode()).hexdigest(),'overflow_checks':'true','toolchain':'nightly-2026-06-01','charon_sha256':actual,'argv':cmd,'includes':includes,'cargo_features':'insecure-spend-fixture,selected-v7-kernels (original host Cargo feature definitions preserved byte-for-byte)','active_aspis_service_reservations_before_launch':reservations,'scope_memory_max_bytes':7*1024**3,'aggregate_reserved_max_bytes':40*1024**3,'phase':'release Rust/MIR compilation as needed + target-only Charon LLBC capture; no translation'}
(stage/'R569-prelaunch.json').write_text(json.dumps(before,indent=2)+'\n')
with (stage/'charon.log').open('w') as out, (stage/'charon.time.log').open('w') as time:
 result=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=out,stderr=time,env=env)
status={'exit_status':result.returncode,'llbc_exists':llbc.is_file(),'llbc_sha256':sha(llbc) if llbc.is_file() else None,'llbc_bytes':llbc.stat().st_size if llbc.is_file() else None,'formal_axioms':'N/A; LLBC capture only','translation':'not run by instruction'}
if llbc.is_file():
 try: status['has_errors']=json.loads(llbc.read_text()).get('has_errors')
 except Exception as e: status['llbc_parse_error']=repr(e)
(stage/'R569-result.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps(status),flush=True)
sys.exit(result.returncode)
'''
def q(s): return repr(s)
remote = REMOTE_SCRIPT.replace("@SOURCE@",q(SOURCE)).replace("@STAGE@",q(STAGE)).replace("@CHARON@",q(CHARON))
remote = remote.replace("@STATE_SHA@",q(STATE_SHA)).replace("@CHARON_SHA@",q(CHARON_SHA)).replace("@RUSTFLAGS@",q(RUSTFLAGS)).replace("@RUSTFLAGS_FILE_SHA@",q(RUSTFLAGS_SHA_FILE))
unit = "aspis-r569-masked-claim-20261004"
systemd = ["systemd-run","--user","--wait","--collect","--pipe",f"--unit={unit}",f"--working-directory={SOURCE}","-p","MemoryHigh=5G","-p","MemoryMax=7G","-p","MemorySwapMax=0","-p","TasksMax=128","-p","RuntimeMaxSec=600s","python3","-c",remote]
(HERE/"launch.json").write_text(json.dumps({"target":"R569 target-only actual masked claim Charon capture", "unit":unit,"source_root":SOURCE,"stage_root":STAGE,"systemd_argv":systemd,"caps":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":0,"TasksMax":128},"charon_sha256":CHARON_SHA,"rustflags_file_sha256":RUSTFLAGS_SHA_FILE,"overflow_checks":True,"translation":False},indent=2)+"\n")
ssh=[*SSH,HOST,shlex.join(systemd)]
with (HERE/"ssh-output.log").open("w") as out:
 r=subprocess.run(ssh,stdout=out,stderr=subprocess.STDOUT)
(HERE/"launch-exit.txt").write_text(str(r.returncode)+"\n")
for rel in ["R569-prelaunch.json","charon.log","charon.time.log","R569-result.json","R569MaskedClaim.llbc"]:
 scp=subprocess.run([*SCP,f"{HOST}:{STAGE}/{rel}",str(HERE/rel)])
 if scp.returncode and rel!="R569MaskedClaim.llbc": raise SystemExit(scp.returncode)
if r.returncode: raise SystemExit(r.returncode)
