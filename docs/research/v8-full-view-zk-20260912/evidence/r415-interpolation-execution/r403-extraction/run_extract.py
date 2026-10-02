#!/usr/bin/env python3
"""Authorized one-root cached release extraction of private interpolate_three_constant_limb; no translation or theorem claim."""
import hashlib
import json
import pathlib
import shlex
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
WORKTREE = HERE.parents[1]
R266_COMMAND = WORKTREE / ".r21-scratch/r266-private-inverse-leaf-extract/extract-command.json"
r266_provenance = json.loads(R266_COMMAND.read_text())
expected_rustflags = r266_provenance["rustflags"]
assert hashlib.sha256(json.dumps(expected_rustflags,separators=(",",":")).encode()).hexdigest() == r266_provenance["rustflags_sha256"]
HOST = "dombarker@100.108.41.90"
SSH_OPTS = ["-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
SOURCE_ROOT = "/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a"
REMOTE_ROOT = "/home/dombarker/project-offloads/aspis-r403-interpolate-three-constant-limb-20261002-a"
SOURCE_REVISION_RECORDED = subprocess.check_output(["git", "-C", str(WORKTREE), "rev-parse", "HEAD"], text=True).strip()
assert SOURCE_REVISION_RECORDED == "d473563212029be91ea1032bfd2ef70ee6d68b73", SOURCE_REVISION_RECORDED
assert len(SOURCE_REVISION_RECORDED) == 40
SOURCE_HASHES = {
    "state_only_poseidon.rs": "4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe",
    "aspis_core_field.rs": "639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499",
    "performance_host_Cargo.toml": "62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c",
    "performance_host_Cargo.lock": "a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814",
}
RUSTFLAGS_SHA256 = r266_provenance["rustflags_sha256"]
START_FROM = ["aspis_statement::state_only_poseidon::interpolate_three_constant_limb"]

REMOTE_SCRIPT = r'''import os,pathlib,hashlib,subprocess,json,shlex
source_root=pathlib.Path("@SOURCE_ROOT@")
experiments=source_root/'docs/research/v8-no-work-100-20260907/experiments'
workspace=experiments/'performance-host'
root=pathlib.Path("@REMOTE_ROOT@")
expected={"state_only_poseidon.rs":"@POSEIDON_HASH@","aspis_core_field.rs":"@FIELD_HASH@","performance_host_Cargo.toml":"@MANIFEST_HASH@","performance_host_Cargo.lock":"@LOCK_HASH@"}
paths={"state_only_poseidon.rs":source_root/'crates/aspis-statement/src/state_only_poseidon.rs',"aspis_core_field.rs":source_root/'crates/aspis-core/src/field.rs',"performance_host_Cargo.toml":workspace/'Cargo.toml',"performance_host_Cargo.lock":workspace/'Cargo.lock'}
actual={k:hashlib.sha256(p.read_bytes()).hexdigest() for k,p in paths.items()}
assert actual==expected,(actual,expected)
poseidon_source=paths["state_only_poseidon.rs"].read_text()
assert "fn interpolate_three_constant_limb(" in poseidon_source
assert "M31::reduce_u64(" in poseidon_source
function_start=poseidon_source.index("fn interpolate_three_constant_limb(")
function_end=poseidon_source.index("\n}",function_start)+2
selected_source=poseidon_source[function_start:function_end]
assert selected_source.count("u64::from(")==6 and selected_source.count("*")==3 and "M31::reduce_u64(" in selected_source
assert not root.exists(),f'extraction root already exists: {root}'
root.mkdir()
os.environ['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:'+os.environ.get('PATH','')
fingerprints=list((workspace/'target/x86_64-unknown-linux-gnu/release/.fingerprint').glob('aspis-v8-performance-host*/bin-aspis-v8-performance-host.json'))
fingerprint_records=[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in fingerprints]
flags=[json.loads(p.read_text())['rustflags'] for p in fingerprints]
assert flags and all(x==flags[0] for x in flags)
assert flags[0]==@EXPECTED_RUSTFLAGS@
rustflags_sha=hashlib.sha256(json.dumps(flags[0],separators=(',',':')).encode()).hexdigest()
assert rustflags_sha=="@RUSTFLAGS_HASH@",rustflags_sha
os.environ['RUSTFLAGS']=shlex.join(flags[0])
manifest=workspace/'Cargo.toml'
charon='/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon'
assert hashlib.sha256(pathlib.Path(charon).read_bytes()).hexdigest()=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
rustc_version=subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','stable','rustc','--version'],text=True).strip()
cargo_version=subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','stable','cargo','--version'],text=True).strip()
nightly_verbose=subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','nightly-2026-06-01','rustc','-vV'],text=True).strip()
nightly_commit=next(x.split(': ',1)[1] for x in nightly_verbose.splitlines() if x.startswith('commit-hash: '))
assert nightly_commit=='14210df0e27ccd7d9e6a05b8085cbd438e4bbc65',nightly_commit
assert rustc_version=='rustc 1.94.1 (e408947bf 2026-03-25)',rustc_version
assert cargo_version=='cargo 1.94.1 (29ea6fb6a 2026-03-24)',cargo_version
release_bin=workspace/'target/x86_64-unknown-linux-gnu/release/aspis-v8-performance-host'
assert release_bin.is_file(),str(release_bin)
release_bin_sha=hashlib.sha256(release_bin.read_bytes()).hexdigest()
assert release_bin.stat().st_size>0
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
running=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)
procs=[]
for p in pathlib.Path('/proc').iterdir():
 if p.name.isdigit():
  try:
   comm=(p/'comm').read_text().strip()
   if comm in ('cargo','rustc','charon'): procs.append({'pid':p.name,'comm':comm})
  except (FileNotFoundError,PermissionError): pass
assert not procs,procs
cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from',@ROOT0@,'--include','aspis_core::field','--include','aspis_statement::state_only_poseidon::interpolate_three_constant_limb','--dest-file',str(root/'R403InterpolateThreeConstantLimb.llbc'),'--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',str(manifest),'--bin','aspis-v8-performance-host']
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
slice_states={}
for n in ('aspisswitchglobal.slice','aspisr214.slice','aspisr215.slice','aspisr387.slice','aspisr396.slice'):
 sr=subprocess.run(['systemctl','show',n,'-p','Id','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent'],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 slice_states[n]={'exit_status':sr.returncode,'output':sr.stdout}
reservation={"meminfo_before":mem,"release_binary":str(release_bin),"release_binary_sha256":release_bin_sha,"release_binary_size":release_bin.stat().st_size,"rustc_stable":rustc_version,"cargo_stable":cargo_version,"charon_build_nightly_release":next(x.split(': ',1)[1] for x in nightly_verbose.splitlines() if x.startswith('release: ')),"charon_build_nightly_commit":nightly_commit,"nightly_rustc_verbose":nightly_verbose,"running_user_services":running,"active_rust_processes_at_gate":procs,"disk_usage_project_offloads":__import__('shutil').disk_usage('/home/dombarker/project-offloads')._asdict(),"verified_source_hashes":actual,"rustflags_sha256":rustflags_sha,"rustflags":flags[0],"release_fingerprint_count":len(fingerprints),"release_fingerprint_files":fingerprint_records,"source_git_dir_present":(source_root/'.git').exists(),"source_revision_recorded":"@SOURCE_REVISION@","existing_slices":slice_states,"active_scopes":subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)}
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr403.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
reservation['r403_slice_before']=subprocess.check_output(['systemctl','show','aspisr403.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
(root/'toolchain.txt').write_text(subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','stable','rustc','--version'],text=True)+subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','stable','cargo','--version'],text=True)+subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','nightly-2026-06-01','rustc','-vV'],text=True)+'charon_sha256='+hashlib.sha256(pathlib.Path(charon).read_bytes()).hexdigest()+'\n')
(root/'extract-command.json').write_text(json.dumps({'command':cmd,'rustflags':flags[0],'rustflags_sha256':rustflags_sha,'verified_source_hashes':actual,'source_revision_recorded':'@SOURCE_REVISION@','source_revision_basis':'current launch-preparation worktree Git revision; frozen source snapshot has no Git metadata','release_binary_sha256':release_bin_sha,'release_binary_size':release_bin.stat().st_size,'release_fingerprint_count':len(fingerprints),'release_fingerprint_files':fingerprint_records,'rustc_stable':rustc_version,'cargo_stable':cargo_version,'charon_build_nightly_rustc_commit':nightly_commit,'monomorphize':False,'start_from':@START_JSON@,'include':['aspis_core::field','aspis_statement::state_only_poseidon::interpolate_three_constant_limb'],'features':'insecure-spend-fixture,selected-v7-kernels'},indent=2))
with (root/'extract.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
cg_rel=next((line.split(':',2)[2] for line in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::')),None)
cg_dir=pathlib.Path('/sys/fs/cgroup')/cg_rel.lstrip('/') if cg_rel is not None else None
cgstats={}
if cg_dir is not None:
 for key in ('memory.current','memory.peak','memory.swap.current','memory.swap.peak','pids.current','pids.max'):
  try: cgstats[key]=(cg_dir/key).read_text().strip()
  except (FileNotFoundError,PermissionError): cgstats[key]=None
(root/'cgroup-measurement.json').write_text(json.dumps({'cgroup_path':str(cg_dir) if cg_dir else None,'stats_after_command_before_scope_exit':cgstats,'measurement_scope':'this exact R403 systemd-run user service and all children'},indent=2))
after={"meminfo_after":{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')},"r403_slice_after":subprocess.check_output(['systemctl','show','aspisr403.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True)}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
result={'charon_exit_status':r.returncode,'llbc_exists':(root/'R403InterpolateThreeConstantLimb.llbc').is_file(),'source_hashes':actual,'source_revision_recorded':'@SOURCE_REVISION@'}
if result['llbc_exists']:
    llbc_path=root/'R403InterpolateThreeConstantLimb.llbc'
    result['llbc_sha256']=hashlib.sha256(llbc_path.read_bytes()).hexdigest()
    artifact=json.loads(llbc_path.read_text())
    translated=artifact.get('translated',{})
    files={f.get("id"):str(f.get("name",{}).get("Local",'')) for f in translated.get('files',[]) if isinstance(f,dict)}
    source_ids={i for i,n in files.items() if n.endswith('/crates/aspis-statement/src/state_only_poseidon.rs') or n.endswith('crates/aspis-statement/src/state_only_poseidon.rs')}
    def last_ident(name):
        if not isinstance(name,list) or not name:return None
        last=name[-1]
        return last.get('Ident',[None])[0] if isinstance(last,dict) and 'Ident' in last else None
    method='interpolate_three_constant_limb'
    candidates=[]
    for row in translated.get('fun_decls',[]):
        meta=row.get('item_meta') or {}; span=meta.get('span',{}).get('data',{})
        if last_ident(meta.get('name'))==method and span.get('file_id') in source_ids:
            candidates.append({'def_id':row.get('def_id'),'name_tail':method,'name':meta.get('name'),'source_line':span.get('beg',{}).get('line'),'source_end_line':span.get('end',{}).get('line'),'is_local':meta.get('is_local'),'body_kind':'Structured' if isinstance(row.get('body'),dict) and 'Structured' in row['body'] else 'non-Structured','body_present':isinstance(row.get('body'),dict) and 'Structured' in row['body']})
    structured=[c for c in candidates if c['source_line']==416 and c['body_present']]
    accepted=(artifact.get('has_errors') is False and len(structured)==1)
    acceptance={'accepted_for_further_review':accepted,'has_errors':artifact.get('has_errors'),'expected_root':START_ROOTS_PLACEHOLDER,'candidate_rows_same_name_in_source_file':candidates,'exact_span_structured_root_count':len(structured),'source_file_ids':sorted(source_ids),'root_locality_reported_not_presupposed':True,'reason':None if accepted else 'LLBC errors present or exact private helper Structured body at state_only_poseidon.rs:416 is absent/non-unique'}
    (root/'acceptance.json').write_text(json.dumps(acceptance,indent=2))
    result['has_errors']=artifact.get('has_errors');result['exact_span_structured_root_count']=len(structured);result['accepted_for_further_review']=accepted
(root/'result.json').write_text(json.dumps(result,indent=2))
print((root/'extract.log').read_text()[-5000:]);print('R403_EXTRACT_EXIT',r.returncode)
raise SystemExit(r.returncode)
'''

def substitute(source, mapping):
    for key, value in mapping.items():
        source = source.replace(key, value)
    return source

mapping={
    "@ROOT0@": repr(START_FROM[0]),
    "@START_JSON@": json.dumps(START_FROM),
    "START_ROOTS_PLACEHOLDER": json.dumps(START_FROM),
    "@SOURCE_ROOT@":SOURCE_ROOT,
    "@REMOTE_ROOT@":REMOTE_ROOT,
    "@POSEIDON_HASH@":SOURCE_HASHES["state_only_poseidon.rs"],
    "@FIELD_HASH@":SOURCE_HASHES["aspis_core_field.rs"],
    "@MANIFEST_HASH@":SOURCE_HASHES["performance_host_Cargo.toml"],
    "@LOCK_HASH@":SOURCE_HASHES["performance_host_Cargo.lock"],
    "@SOURCE_REVISION@":SOURCE_REVISION_RECORDED,
    "@RUSTFLAGS_HASH@":RUSTFLAGS_SHA256,
    "@EXPECTED_RUSTFLAGS@":repr(expected_rustflags),
}
remote_script=substitute(REMOTE_SCRIPT,mapping)
argv=["systemd-run","--user","--wait","--collect","--pipe","--unit=aspis-r403-interpolate-three-constant-limb-extract","--working-directory="+SOURCE_ROOT,"-p","MemoryHigh=5G","-p","MemoryMax=7G","-p","MemorySwapMax=0","-p","TasksMax=128","python3","-c",remote_script]
ssh_argv=["ssh",*SSH_OPTS,HOST,shlex.join(argv)]
(HERE/"launch.json").write_text(json.dumps({"local_runner":str(pathlib.Path(__file__).resolve()),"local_runner_sha256":hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),"remote_source_root":SOURCE_ROOT,"remote_output_root":REMOTE_ROOT,"ssh_argv":ssh_argv,"systemd_argv":argv,"caps":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128},"verified_source_hashes":SOURCE_HASHES,"rustflags_sha256":RUSTFLAGS_SHA256,"rustflags_from_R266_saved_command":expected_rustflags},indent=2)+"\n")
with (HERE/"ssh-output.log").open("w") as out: result=subprocess.run(ssh_argv,stdout=out,stderr=subprocess.STDOUT)
print((HERE/"ssh-output.log").read_text())
for name in ("extract-command.json","extract.log","host-reservation-before.json","host-reservation-after.json","cgroup-measurement.json","result.json","acceptance.json","R403InterpolateThreeConstantLimb.llbc","toolchain.txt"):
    copied=subprocess.run(["scp",*SSH_OPTS,f"{HOST}:{REMOTE_ROOT}/{name}",str(HERE/name)])
    if copied.returncode and name not in ("R403InterpolateThreeConstantLimb.llbc","acceptance.json"):
        sys.exit(copied.returncode)
if result.returncode:
    sys.exit(result.returncode)
acceptance_path=HERE/"acceptance.json"
if not acceptance_path.is_file() or not json.loads(acceptance_path.read_text()).get("accepted_for_further_review"):
    sys.exit(2)
sys.exit(0)
