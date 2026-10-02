#!/usr/bin/env python3
"""Prepare the lead-selected R327 focused R297 extraction with four narrow Iterator::try_fold/ControlFlow include patterns; this runner is launch-gated by review."""
import hashlib
import json
import pathlib
import shlex
import subprocess
import sys

if __import__("os").environ.get("R327_ALLOW_LAUNCH") != "1":
    raise SystemExit("unlaunched preparation: set R327_ALLOW_LAUNCH=1 only after lead approval")

HERE = pathlib.Path(__file__).resolve().parent
WORKTREE = HERE.parents[1]
R266_COMMAND = WORKTREE / ".r21-scratch/r266-private-inverse-leaf-extract/extract-command.json"
r266_provenance = json.loads(R266_COMMAND.read_text())
expected_rustflags = r266_provenance["rustflags"]
assert hashlib.sha256(json.dumps(expected_rustflags,separators=(",",":")).encode()).hexdigest() == r266_provenance["rustflags_sha256"]
HOST = "dombarker@100.108.41.90"
SSH_OPTS = ["-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null"]
SOURCE_ROOT = "/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a"
REMOTE_ROOT = "/home/dombarker/project-offloads/aspis-r327-private-batch-source-try-fold-20261002-a"
SOURCE_REVISION_RECORDED = subprocess.check_output(["git", "-C", str(WORKTREE), "rev-parse", "HEAD"], text=True).strip()  # frozen remote source snapshot itself has no .git
assert len(SOURCE_REVISION_RECORDED) == 40
SOURCE_HASHES = {
    "r110_norm.rs": "8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e",
    "circle_norm.rs": "3f0882366674d5d41e365e62787d85b62076e6077697e9f756e135ce12aedbd2",
    "line_norm.rs": "4fb70d37d16053a74e08716433af45998e7ddd13fc5dca7b1c86505ed7e2c528",
    "joined_inverse.rs": "ef9b45ce8a7ffbcf57564bcc1348cae3197a09fbbbd529ffca632b778281efeb",
    "aspis_core_field.rs": "639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499",
    "performance_host_Cargo.toml": "62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c",
    "performance_host_Cargo.lock": "a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814",
}
RUSTFLAGS_SHA256 = r266_provenance["rustflags_sha256"]
START_FROM = ["crate::circle_norm::joined_inverse::line_norm::r110_norm::batch"]
assert len(START_FROM) == 1 and START_FROM[0].endswith("::r110_norm::batch")
assert not set(START_FROM) & set(r266_provenance["start_from"]), "R283 root must not duplicate R266 roots"
assert r266_provenance["start_from"] == ["crate::circle_norm::joined_inverse::line_norm::r110_norm::B::neg", "crate::circle_norm::joined_inverse::line_norm::r110_norm::B::inv"]
assert r266_provenance["verified_source_hashes"] == {**SOURCE_HASHES}

REMOTE_SCRIPT = r'''import os,pathlib,hashlib,subprocess,json,shlex
source_root=pathlib.Path("@SOURCE_ROOT@")
experiments=source_root/'docs/research/v8-no-work-100-20260907/experiments'
workspace=experiments/'performance-host'
root=pathlib.Path("@REMOTE_ROOT@")
expected={"r110_norm.rs":"8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e","circle_norm.rs":"@CIRCLE_HASH@","line_norm.rs":"@LINE_HASH@","joined_inverse.rs":"@JOINED_HASH@","aspis_core_field.rs":"@FIELD_HASH@","performance_host_Cargo.toml":"@MANIFEST_HASH@","performance_host_Cargo.lock":"@LOCK_HASH@"}
paths={"r110_norm.rs":experiments/'r110_norm.rs',"circle_norm.rs":experiments/'circle_norm.rs',"line_norm.rs":experiments/'line_norm.rs',"joined_inverse.rs":experiments/'joined_inverse.rs',"aspis_core_field.rs":source_root/'crates/aspis-core/src/field.rs',"performance_host_Cargo.toml":workspace/'Cargo.toml',"performance_host_Cargo.lock":workspace/'Cargo.lock'}
actual={k:hashlib.sha256(p.read_bytes()).hexdigest() for k,p in paths.items()}
assert actual==expected,(actual,expected)
r110_source=paths["r110_norm.rs"].read_text()
field_source=paths["aspis_core_field.rs"].read_text()
assert "fn batch(" in r110_source
assert not root.exists(),f'extraction root already exists: {root}'
root.mkdir()
os.environ['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:'+os.environ.get('PATH','')
fingerprints=list((workspace/'target/x86_64-unknown-linux-gnu/release/.fingerprint').glob('aspis-v8-performance-host*/bin-aspis-v8-performance-host.json'))
flags=[json.loads(p.read_text())['rustflags'] for p in fingerprints]
assert flags and all(x==flags[0] for x in flags)
assert flags[0]==@EXPECTED_RUSTFLAGS@
rustflags_sha=hashlib.sha256(json.dumps(flags[0],separators=(',',':')).encode()).hexdigest()
assert rustflags_sha=="@RUSTFLAGS_HASH@",rustflags_sha
os.environ['RUSTFLAGS']=shlex.join(flags[0])
manifest=workspace/'Cargo.toml'
charon='/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon'
assert hashlib.sha256(pathlib.Path(charon).read_bytes()).hexdigest() == 'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from',@ROOT0@,'--include','core::option','--include','aspis_core::field','--include','core::iter::adapters::chain::Chain','--include','core::iter::adapters::chain::_::next','--include','core::iter::adapters::chain::_::try_fold','--include','core::iter::traits::iterator::Iterator::any','--include','core::iter::traits::iterator::Iterator::chain','--include','core::slice::iter::_::any','--include','core::slice::_::last','--include','core::iter::traits::iterator::Iterator::try_fold','--include','core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::branch','--include','core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::from_output','--include','core::ops::control_flow::{impl core::ops::try_trait::FromResidual<core::ops::control_flow::ControlFlow<_,core::convert::Infallible>> for core::ops::control_flow::ControlFlow<_,_>}::from_residual','--monomorphize','--dest-file',str(root/'R327PrivateBatchSourceTryFold.llbc'),'--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',str(manifest),'--bin','aspis-v8-performance-host']
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
reservation={"meminfo_before":mem,"disk_usage_project_offloads":__import__('shutil').disk_usage('/home/dombarker/project-offloads')._asdict(),"verified_source_hashes":actual,"rustflags_sha256":rustflags_sha,"rustflags":flags[0],"source_git_dir_present":(source_root/'.git').exists(),"source_revision_recorded":"@SOURCE_REVISION@","existing_slices":{n:subprocess.check_output(['systemctl','show',n,'-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent'],text=True) for n in ('aspisswitchglobal.slice','aspisr214.slice','aspisr215.slice')},"active_scopes":subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)}
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr327.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
reservation['r327_slice_before']=subprocess.check_output(['systemctl','show','aspisr327.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
channel=subprocess.check_output([charon,'toolchain-version'],text=True).strip()
assert channel == 'nightly-2026-06-01', channel
sysroot=subprocess.check_output([charon,'toolchain-path'],text=True).strip()
driver=pathlib.Path(charon).with_name('charon-driver')
rustc_version=subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run',channel,'rustc','--version','--verbose'],text=True)
cargo_version=subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run',channel,'cargo','--version'],text=True)
assert '14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' in rustc_version, rustc_version
ldd=subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run',channel,'ldd',str(driver)],text=True)
driver_libraries=list(pathlib.Path(sysroot,'lib').glob('librustc_driver-*.so'))
assert len(driver_libraries)==1,driver_libraries
(root/'toolchain.txt').write_text('charon_version='+subprocess.check_output([charon,'version'],text=True).strip()+'\ncharon_toolchain='+channel+'\ncharon_sysroot='+sysroot+'\n'+rustc_version+cargo_version+'charon_sha256='+hashlib.sha256(pathlib.Path(charon).read_bytes()).hexdigest()+'\ncharon_driver_sha256='+hashlib.sha256(driver.read_bytes()).hexdigest()+'\nrustc_driver_library='+str(driver_libraries[0])+'\nrustc_driver_library_sha256='+hashlib.sha256(driver_libraries[0].read_bytes()).hexdigest()+'\n'+ldd)
(root/'extract-command.json').write_text(json.dumps({'command':cmd,'rustflags':flags[0],'rustflags_sha256':rustflags_sha,'verified_source_hashes':actual,'source_revision_recorded':'@SOURCE_REVISION@','source_revision_basis':'current launch-preparation worktree Git revision; frozen source snapshot has no Git metadata; refresh at actual launch','monomorphize':True,'start_from':@START_JSON@,'include':['core::option','aspis_core::field','core::iter::adapters::chain::Chain','core::iter::adapters::chain::_::next','core::iter::adapters::chain::_::try_fold','core::iter::traits::iterator::Iterator::any','core::iter::traits::iterator::Iterator::chain','core::slice::iter::_::any','core::slice::_::last','core::iter::traits::iterator::Iterator::try_fold','core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::branch','core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::from_output','core::ops::control_flow::{impl core::ops::try_trait::FromResidual<core::ops::control_flow::ControlFlow<_,core::convert::Infallible>> for core::ops::control_flow::ControlFlow<_,_>}::from_residual'],'features':'insecure-spend-fixture,selected-v7-kernels'},indent=2))
with (root/'extract.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
after={"meminfo_after":{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')},"r327_slice_after":subprocess.check_output(['systemctl','show','aspisr327.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True)}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
llbc=root/'R327PrivateBatchSourceTryFold.llbc'
result={'charon_exit_status':r.returncode,'llbc_exists':llbc.is_file(),'source_hashes':actual,'source_revision_recorded':'@SOURCE_REVISION@','start_from':@START_JSON@,'include':['core::option','aspis_core::field','core::iter::adapters::chain::Chain','core::iter::adapters::chain::_::next','core::iter::adapters::chain::_::try_fold','core::iter::traits::iterator::Iterator::any','core::iter::traits::iterator::Iterator::chain','core::slice::iter::_::any','core::slice::_::last','core::iter::traits::iterator::Iterator::try_fold','core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::branch','core::ops::control_flow::{impl core::ops::try_trait::Try for core::ops::control_flow::ControlFlow<_,_>}::from_output','core::ops::control_flow::{impl core::ops::try_trait::FromResidual<core::ops::control_flow::ControlFlow<_,core::convert::Infallible>> for core::ops::control_flow::ControlFlow<_,_>}::from_residual']}
if result['llbc_exists']:
 result['llbc_sha256']=hashlib.sha256(llbc.read_bytes()).hexdigest()
 data=json.loads(llbc.read_text()); tr=data['translated']; result['has_errors']=data['has_errors']
 rootfun=next((x for x in tr['fun_decls'] if isinstance(x,dict) and x.get('def_id')==0),None)
 result['root_fun0']={'present':rootfun is not None,'local':rootfun.get('item_meta',{}).get('is_local') if rootfun else None,'body_present':rootfun is not None and rootfun.get('body') not in (None,'Opaque'),'body_kind':'Opaque' if rootfun is not None and rootfun.get('body')=='Opaque' else ('present' if rootfun is not None and rootfun.get('body') is not None else None)}
 def named(row):
  parts=[]
  for part in row.get('item_meta',{}).get('name',[]):
   if 'Ident' in part: parts.append(part['Ident'][0])
   else: parts.append(str(part))
  return '::'.join(parts)
 needles=('core::iter::adapters::chain','core::iter::traits::iterator::Iterator::any','core::iter::traits::iterator::Iterator::chain','try_fold','core::slice::iter','core::slice','Chain','ControlFlow','from_output','from_residual','::branch')
 result['selected_body_census']={'functions':[{'def_id':x['def_id'],'name':named(x),'body_status':'opaque' if x.get('body')=='Opaque' else ('body' if x.get('body') is not None else 'absent'),'local':x.get('item_meta',{}).get('is_local'),'opacity':x.get('item_meta',{}).get('opacity')} for x in tr.get('fun_decls',[]) if isinstance(x,dict) and any(n in named(x) for n in needles)],'types':[{'def_id':x['def_id'],'name':named(x),'opacity':x.get('item_meta',{}).get('opacity')} for x in tr.get('type_decls',[]) if isinstance(x,dict) and any(n in named(x) for n in needles)]}
 result['declaration_counts']={k:sum(isinstance(x,dict) for x in tr.get(k,[])) for k in ('type_decls','fun_decls','global_decls','trait_decls','trait_impls')}
(root/'result.json').write_text(json.dumps(result,indent=2))
print((root/'extract.log').read_text()[-5000:]);print('R327_EXTRACT_EXIT',r.returncode)
raise SystemExit(r.returncode)
'''

def substitute(source, mapping):
    for key, value in mapping.items():
        source = source.replace(key, value)
    return source

mapping={
    "@ROOT0@": repr(START_FROM[0]),
    "@START_JSON@": json.dumps(START_FROM),
    "@SOURCE_ROOT@":SOURCE_ROOT,
    "@REMOTE_ROOT@":REMOTE_ROOT,
    "@CIRCLE_HASH@":SOURCE_HASHES["circle_norm.rs"],
    "@LINE_HASH@":SOURCE_HASHES["line_norm.rs"],
    "@JOINED_HASH@":SOURCE_HASHES["joined_inverse.rs"],
    "@FIELD_HASH@":SOURCE_HASHES["aspis_core_field.rs"],
    "@MANIFEST_HASH@":SOURCE_HASHES["performance_host_Cargo.toml"],
    "@LOCK_HASH@":SOURCE_HASHES["performance_host_Cargo.lock"],
    "@SOURCE_REVISION@":SOURCE_REVISION_RECORDED,
    "@RUSTFLAGS_HASH@":RUSTFLAGS_SHA256,
    "@EXPECTED_RUSTFLAGS@":repr(expected_rustflags),
}
remote_script=substitute(REMOTE_SCRIPT,mapping)
argv=["systemd-run","--user","--wait","--collect","--pipe","--unit=aspis-r327-private-batch-source-try-fold","--working-directory="+SOURCE_ROOT,"-p","MemoryHigh=5G","-p","MemoryMax=7G","-p","MemorySwapMax=0","-p","TasksMax=128","python3","-c",remote_script]
ssh_argv=["ssh",*SSH_OPTS,HOST,shlex.join(argv)]
(HERE/"launch.json").write_text(json.dumps({"local_runner":str(pathlib.Path(__file__).resolve()),"local_runner_sha256":hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),"remote_source_root":SOURCE_ROOT,"remote_output_root":REMOTE_ROOT,"ssh_argv":ssh_argv,"systemd_argv":argv,"caps":{"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128},"verified_source_hashes":SOURCE_HASHES,"rustflags_sha256":RUSTFLAGS_SHA256,"rustflags_from_R266_saved_command":expected_rustflags},indent=2)+"\n")
with (HERE/"ssh-output.log").open("w") as out: result=subprocess.run(ssh_argv,stdout=out,stderr=subprocess.STDOUT)
print((HERE/"ssh-output.log").read_text())
for name in ("extract-command.json","extract.log","host-reservation-before.json","host-reservation-after.json","result.json","R327PrivateBatchSourceTryFold.llbc","toolchain.txt"):
    copied=subprocess.run(["scp",*SSH_OPTS,f"{HOST}:{REMOTE_ROOT}/{name}",str(HERE/name)])
    if copied.returncode and name!="R327PrivateBatchSourceTryFold.llbc":
        sys.exit(copied.returncode)
sys.exit(result.returncode)
