#!/usr/bin/env python3
"""Prepare/launch the isolated R282 try_norm scalar map-closure extraction."""
import hashlib
import json
import pathlib
import shlex
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
WORKTREE = HERE.parents[1]
R266_COMMAND = WORKTREE / '.r21-scratch/r266-private-inverse-leaf-extract/extract-command.json'
r266 = json.loads(R266_COMMAND.read_text())
RUSTFLAGS = r266['rustflags']
RUSTFLAGS_SHA256 = r266['rustflags_sha256']
assert hashlib.sha256(json.dumps(RUSTFLAGS, separators=(',', ':')).encode()).hexdigest() == RUSTFLAGS_SHA256
SOURCE_HASHES = {
    'r110_norm.rs': '8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e',
    'circle_norm.rs': '3f0882366674d5d41e365e62787d85b62076e6077697e9f756e135ce12aedbd2',
    'line_norm.rs': '4fb70d37d16053a74e08716433af45998e7ddd13fc5dca7b1c86505ed7e2c528',
    'joined_inverse.rs': 'ef9b45ce8a7ffbcf57564bcc1348cae3197a09fbbbd529ffca632b778281efeb',
    'aspis_core_field.rs': '639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499',
    'performance_host_Cargo.toml': '62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c',
    'performance_host_Cargo.lock': 'a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814',
}
assert r266['verified_source_hashes'] == SOURCE_HASHES
assert r266['include'] == ['core::option', 'aspis_core::field']
assert r266['features'] == 'insecure-spend-fixture,selected-v7-kernels'
assert r266['monomorphize'] is False
assert r266['rustflags_sha256'] == 'f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613'

HOST = 'dombarker@100.108.41.90'
SSH_OPTS = ['-o', 'BatchMode=yes', '-o', 'StrictHostKeyChecking=no', '-o', 'UserKnownHostsFile=/dev/null']
SOURCE_ROOT = '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
REMOTE_ROOT = '/home/dombarker/project-offloads/aspis-r282-private-norm-closures-extract-20261002-a'
UNIT = 'aspis-r282-private-norm-closures-extract'
SOURCE_REVISION_RECORDED = '380c7d46c9719dcfcab601fac2607861d47dee02'
START_FROM = 'crate::circle_norm::joined_inverse::line_norm::r110_norm::try_norm::_::call_once'

REMOTE_SCRIPT = r'''import os,pathlib,hashlib,subprocess,json,shlex,re
source_root=pathlib.Path("@SOURCE_ROOT@")
experiments=source_root/'docs/research/v8-no-work-100-20260907/experiments'
workspace=experiments/'performance-host'
root=pathlib.Path("@REMOTE_ROOT@")
expected={"r110_norm.rs":"@R110_HASH@","circle_norm.rs":"@CIRCLE_HASH@","line_norm.rs":"@LINE_HASH@","joined_inverse.rs":"@JOINED_HASH@","aspis_core_field.rs":"@FIELD_HASH@","performance_host_Cargo.toml":"@MANIFEST_HASH@","performance_host_Cargo.lock":"@LOCK_HASH@"}
paths={"r110_norm.rs":experiments/'r110_norm.rs',"circle_norm.rs":experiments/'circle_norm.rs',"line_norm.rs":experiments/'line_norm.rs',"joined_inverse.rs":experiments/'joined_inverse.rs',"aspis_core_field.rs":source_root/'crates/aspis-core/src/field.rs',"performance_host_Cargo.toml":workspace/'Cargo.toml',"performance_host_Cargo.lock":workspace/'Cargo.lock'}
actual={k:hashlib.sha256(p.read_bytes()).hexdigest() for k,p in paths.items()}
assert actual==expected,(actual,expected)
r110_source=paths['r110_norm.rs'].read_text()
assert 'pub(super) fn try_norm(' in r110_source
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
cmd=[charon,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from',"@ROOT_PATTERN@",'--include','core::option','--include','aspis_core::field','--dest-file',str(root/'R282PrivateNormClosures.llbc'),'--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',str(manifest),'--bin','aspis-v8-performance-host']
mem={k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')}
assert int(mem['MemAvailable'].split()[0])>=24*1024*1024,mem
reservation={"meminfo_before":mem,"disk_usage_project_offloads":__import__('shutil').disk_usage('/home/dombarker/project-offloads')._asdict(),"verified_source_hashes":actual,"rustflags_sha256":rustflags_sha,"rustflags":flags[0],"source_git_dir_present":(source_root/'.git').exists(),"source_revision_recorded":"@SOURCE_REVISION@","existing_slices":{n:subprocess.check_output(['systemctl','show',n,'-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent'],text=True) for n in ('aspisswitchglobal.slice','aspisr214.slice','aspisr215.slice')},"active_scopes":subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--no-legend'],text=True)}
subprocess.run(['sudo','-n','systemctl','set-property','--runtime','aspisr282.slice','MemoryHigh=5G','MemoryMax=7G','MemorySwapMax=0','TasksMax=128'],check=True)
reservation['r282_slice_before']=subprocess.check_output(['systemctl','show','aspisr282.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak'],text=True)
(root/'host-reservation-before.json').write_text(json.dumps(reservation,indent=2))
(root/'toolchain.txt').write_text(subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','stable','rustc','--version'],text=True)+subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run','stable','cargo','--version'],text=True)+'charon_sha256='+hashlib.sha256(pathlib.Path(charon).read_bytes()).hexdigest()+'\n')
(root/'extract-command.json').write_text(json.dumps({'command':cmd,'rustflags':flags[0],'rustflags_sha256':rustflags_sha,'verified_source_hashes':actual,'source_revision_recorded':'@SOURCE_REVISION@','source_revision_basis':'launch worktree Git revision; frozen source snapshot has no Git metadata','monomorphize':False,'start_from':["@ROOT_PATTERN@"],'include':['core::option','aspis_core::field'],'features':'insecure-spend-fixture,selected-v7-kernels'},indent=2))
with (root/'extract.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],stdout=f,stderr=subprocess.STDOUT)
llbc_path=root/'R282PrivateNormClosures.llbc'
assert r.returncode==0 and llbc_path.is_file(),(r.returncode,llbc_path.exists())
# Read and validate metadata only; the extracted LLBC bytes are left untouched.
doc=json.loads(llbc_path.read_text())
translated=doc['translated']
base=['aspis_v8_performance_host','circle_norm','joined_inverse','line_norm','r110_norm','try_norm']
def segments(row):
    out=[]
    for item in row.get('name') or []:
        if 'Ident' in item: out.append(item['Ident'][0])
        elif 'Impl' in item:
            impl=item['Impl']; out.append('ImplTrait'+str(impl['Trait']) if 'Trait' in impl else 'Impl')
        else: out.append(str(next(iter(item))))
    return out
closures=[]
for row in translated.get('fun_decls',[]):
    if not isinstance(row,dict): continue
    meta=row.get('item_meta')
    if not isinstance(meta,dict): continue
    path=segments(meta)
    if path[:len(base)]!=base or len(path)<len(base)+2: continue
    method=path[-1]
    if method not in ('call_once','call_mut'): continue
    closures.append({'method':method,'path':path,'def_id':row.get('def_id'),'source_text':meta.get('source_text'),'span':meta.get('span'),'signature':row.get('signature'),'generics':row.get('generics')})
root_rows=[row for row in closures if row['method']=='call_once']
mut_rows=[row for row in closures if row['method']=='call_mut']
valid = doc['has_errors'] is False and len(root_rows)==3 and len(mut_rows)==3
validation={'root_pattern':"@ROOT_PATTERN@",'root_local_call_once_count':len(root_rows),'call_once':root_rows,'transitive_call_mut_count':len(mut_rows),'call_mut':mut_rows,'llbc_sha256':hashlib.sha256(llbc_path.read_bytes()).hexdigest(),'llbc_rewritten':False,'has_errors':doc['has_errors'],'accepted_for_further_review':valid}
(root/'closure-counts.json').write_text(json.dumps(validation,indent=2))
after={'meminfo_after':{k:v for k,v in (line.split(':',1) for line in pathlib.Path('/proc/meminfo').read_text().splitlines()) if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree')},'r282_slice_after':subprocess.check_output(['systemctl','show','aspisr282.slice','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax','-p','MemoryCurrent','-p','MemoryPeak','-p','MemorySwapCurrent','-p','MemorySwapPeak'],text=True)}
(root/'host-reservation-after.json').write_text(json.dumps(after,indent=2))
result={'charon_exit_status':r.returncode,'llbc_exists':llbc_path.is_file(),'llbc_sha256':hashlib.sha256(llbc_path.read_bytes()).hexdigest(),'source_hashes':actual,'source_revision_recorded':'@SOURCE_REVISION@','closure_counts':{'call_once':len(root_rows),'call_mut':len(mut_rows)},'has_errors':doc['has_errors'],'accepted_for_further_review':valid}
(root/'result.json').write_text(json.dumps(result,indent=2))
print((root/'extract.log').read_text()[-5000:]);print('R282_EXTRACT_EXIT',r.returncode);print('R282_METADATA_ACCEPTED',valid)
raise SystemExit(0 if valid else 1)
'''


def replace(template, mapping):
    for old, new in mapping.items():
        template = template.replace(old, new)
    return template

mapping = {
    '@SOURCE_ROOT@': SOURCE_ROOT, '@REMOTE_ROOT@': REMOTE_ROOT,
    '@R110_HASH@': SOURCE_HASHES['r110_norm.rs'], '@CIRCLE_HASH@': SOURCE_HASHES['circle_norm.rs'],
    '@LINE_HASH@': SOURCE_HASHES['line_norm.rs'], '@JOINED_HASH@': SOURCE_HASHES['joined_inverse.rs'],
    '@FIELD_HASH@': SOURCE_HASHES['aspis_core_field.rs'], '@MANIFEST_HASH@': SOURCE_HASHES['performance_host_Cargo.toml'],
    '@LOCK_HASH@': SOURCE_HASHES['performance_host_Cargo.lock'], '@EXPECTED_RUSTFLAGS@': repr(RUSTFLAGS),
    '@RUSTFLAGS_HASH@': RUSTFLAGS_SHA256, '@SOURCE_REVISION@': SOURCE_REVISION_RECORDED,
    '@ROOT_PATTERN@': START_FROM,
}
remote_script = replace(REMOTE_SCRIPT, mapping)
argv = ['systemd-run','--user','--wait','--collect','--pipe','--unit='+UNIT,
        '--working-directory='+SOURCE_ROOT,'-p','MemoryHigh=5G','-p','MemoryMax=7G',
        '-p','MemorySwapMax=0','-p','TasksMax=128','python3','-c',remote_script]
ssh_argv = ['ssh', *SSH_OPTS, HOST, shlex.join(argv)]
# Persist exact prepared command; this script is not executed by preparing the files.
(HERE / 'launch.json').write_text(json.dumps({
    'local_runner': str(pathlib.Path(__file__).resolve()),
    'local_runner_sha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
    'remote_source_root': SOURCE_ROOT, 'remote_output_root': REMOTE_ROOT,
    'systemd_unit': UNIT, 'start_from': [START_FROM], 'ssh_argv': ssh_argv,
    'systemd_argv': argv, 'caps': {'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},
    'verified_source_hashes': SOURCE_HASHES, 'rustflags_sha256': RUSTFLAGS_SHA256,
    'rustflags_from_R266_saved_command': RUSTFLAGS,
    'source_revision_recorded': SOURCE_REVISION_RECORDED,
    'monomorphize': False, 'includes': ['core::option','aspis_core::field'],
}, indent=2) + '\n')
with (HERE / 'ssh-output.log').open('w') as output:
    result = subprocess.run(ssh_argv, stdout=output, stderr=subprocess.STDOUT)
print((HERE / 'ssh-output.log').read_text())
for name in ('extract-command.json','extract.log','host-reservation-before.json','host-reservation-after.json',
             'result.json','closure-counts.json','R282PrivateNormClosures.llbc','toolchain.txt'):
    copied = subprocess.run(['scp', *SSH_OPTS, f'{HOST}:{REMOTE_ROOT}/{name}', str(HERE / name)])
    if copied.returncode and name != 'R282PrivateNormClosures.llbc':
        raise SystemExit(copied.returncode)
raise SystemExit(result.returncode)
