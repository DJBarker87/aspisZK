#!/usr/bin/env python3
"""One approved source-only Charon capture of selected R117 owned_primal::fold."""
import hashlib, json, pathlib, shlex, subprocess, sys
HERE = pathlib.Path(__file__).resolve().parent
HOST = 'dombarker@100.108.41.90'
SSH_OPTS = ['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
SRC = '/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
REMOTE = '/home/dombarker/project-offloads/aspis-r664-owned-fold-option-wrappers-capture-20261004-a'
UNIT = 'aspis-r664-owned-fold-option-wrappers-capture-20261004-a'
CHARON = '/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon'
CHARON_SHA = 'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
FILES = {
 'relation_callback.rs':'docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs',
 'r17_host_relation.rs':'docs/research/v8-no-work-100-20260907/experiments/r17_host_relation.rs',
 'r17_owned_primal.rs':'docs/research/v8-no-work-100-20260907/experiments/r17_owned_primal.rs',
 'r117_primal.rs':'docs/research/v8-no-work-100-20260907/experiments/r117_primal.rs',
 'performance.rs':'docs/research/v8-no-work-100-20260907/experiments/performance.rs',
 'performance_host_Cargo.toml':'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml',
 'performance_host_Cargo.lock':'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.lock',
 'field.rs':'crates/aspis-core/src/field.rs',
}
PINS = {
 'relation_callback.rs':'4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f',
 'r17_host_relation.rs':'3b7a5040509e0c3ad5e421e49a4f6d1d106c5adabfc2bf891bf8685c66b4b801',
 'r17_owned_primal.rs':'4c4dca09aee38d16bdd2ff39d8c841b973cd44cd2f232061ee173b0caa131a56',
 'r117_primal.rs':'227bcc7790a424d856562d68b0772882930c1e40100d72ba7e0685724b9f7e7f',
 'performance.rs':'4c575d4d1004bf39b0bb1f8069495e315e63a7ec9f423a60ec93f3487f4eb8b5',
 'performance_host_Cargo.toml':'62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c',
 'performance_host_Cargo.lock':'a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814',
 'field.rs':'639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499',
}
FLAGS = ['--cfg','v8_positive_transfer','--cfg','v8_complete','--cfg','v8_performance_fast','--cfg','v8_structured','--cfg','v8_fine_profile','--cfg','v8_batch_m','--cfg','v8_tower_batch','--cfg','v8_query_kernels','--cfg','v8_fused_rows','--cfg','v8_shared_weights','--cfg','v8_block_horner','--cfg','v8_gamma_wrap','--cfg','v8_reuse_gamma','--cfg','v8_grouped_linear','--cfg','v8_query_shared','--cfg','v8_range_m31','--cfg','v8_range_cm31','--cfg','v8_sparse_groups','--cfg','v8_range_dots','--cfg','v8_cm_schoolbook','--cfg','v8_prepared_schoolbook','--cfg','v8_quiet_profile','--cfg','v8_payment_extraction','--cfg','v8_performance','--cfg','v8_qm_hybrid','--cfg','v8_qm_lazy_c0','--cfg','v8_gamma_partial','-A','dead_code','-A','unexpected_cfgs','--cfg','v8_circle_norm','--cfg','v8_chord_norm','--cfg','v8_joined_inverse','--cfg','v8_split_inverse','--cfg','v8_line_norm','--cfg','v8_quotient_fused','--cfg','v8_affine_primal','--cfg','v8_compact_workspace','--cfg','v8_gamma_fixed','--cfg','v8_merkle_slices','--cfg','v8_merkle_borrow','--cfg','v8_leaf_record']
FLAGS_SHA = 'f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613'
CARGO = SRC + '/docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'
CMD = [CHARON,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::r17_host_relation::owned_primal::fold','--include','aspis_core::field','--include','core::option::Option::unwrap_or_else','--include','core::option::{impl core::ops::try_trait::Try for core::option::Option<_>}::branch','--include','core::option::{impl core::ops::try_trait::FromResidual<core::option::Option<core::convert::Infallible>> for core::option::Option<_>}::from_residual','--dest-file',REMOTE+'/R664OwnedPrimalFoldOptionWrappers.llbc','--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',CARGO,'--bin','aspis-v8-performance-host']
remote = r'''import hashlib,json,os,pathlib,subprocess,sys
root=pathlib.Path(__REMOTE__); charon=pathlib.Path(__CHARON__)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert not root.exists(),root
assert sha(charon)==__CHARON_SHA__
paths={k:__SRC__+'/'+v for k,v in __FILES__.items()}; pins=__PINS__
assert {k:sha(pathlib.Path(v)) for k,v in paths.items()}==pins
flags=__FLAGS__
assert hashlib.sha256(json.dumps(flags,separators=(',',':')).encode()).hexdigest()==__FLAGS_SHA__
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'},limits
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True); reservations=[]
for line in units.splitlines():
 w=line.split()
 if w and w[0].startswith('aspis'):
  v=subprocess.check_output(['systemctl','--user','show',w[0],'-p','MemoryMax'],text=True).strip().split('=',1)[1]
  if v.isdigit(): reservations.append((w[0],int(v)))
assert sum(v for _,v in reservations)<=40*1024**3,reservations
root.mkdir(mode=0o700)
cmd=__CMD__
env=dict(os.environ); env['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:'+env.get('PATH',''); env['RUSTFLAGS']=' '.join(flags); env['CARGO_INCREMENTAL']='0'
(root/'capture-command.json').write_text(json.dumps({'target':'selected R117 owned_primal::fold plus exact Option wrapper includes; capture only','argv':cmd,'excluded_options':['--monomorphize','--consts values'],'charon_sha256':__CHARON_SHA__,'frozen_source_revision':'6677d5f1310ff7373301fbd79f186278f772e68a (external frozen snapshot; snapshot has no .git metadata)','source_hashes':pins,'rustflags':flags,'rustflags_sha256':__FLAGS_SHA__,'features':'insecure-spend-fixture,selected-v7-kernels','cargo_mode':'offline, locked, release, jobs=1','caps':limits,'reservations':reservations},indent=2)+'\n')
with (root/'charon.stdout.log').open('w') as out,(root/'charon.stderr.log').open('w') as err:
 r=subprocess.run(['/usr/bin/time','-v','-o',str(root/'charon.time.log'),*cmd],stdout=out,stderr=err,env=env)
llbc=root/'R664OwnedPrimalFoldOptionWrappers.llbc'
result={'exit_status':r.returncode,'llbc_exists':llbc.exists(),'charon_sha256':__CHARON_SHA__,'formal_axioms':'N/A; source capture only'}
if llbc.exists():
 result['llbc_sha256']=sha(llbc); result['llbc_bytes']=llbc.stat().st_size
 try:
  d=json.loads(llbc.read_text()); result['has_errors']=d.get('has_errors'); tr=d.get('translated',{}); result['counts']={k:len(tr.get(k,[])) for k in ['fun_decls','type_decls','global_decls','trait_decls','trait_impls','ordered_decls']}
 except Exception as e: result['llbc_parse_error']=repr(e)
(root/'result.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result)); sys.exit(r.returncode)
'''
for key, val in {'__REMOTE__':REMOTE,'__CHARON__':CHARON,'__CHARON_SHA__':CHARON_SHA,'__SRC__':SRC,'__FILES__':FILES,'__PINS__':PINS,'__FLAGS__':FLAGS,'__FLAGS_SHA__':FLAGS_SHA,'__CMD__':CMD}.items():
    remote=remote.replace(key,repr(val))
systemd=['systemd-run','--user','--wait','--collect','--pipe','--unit='+UNIT,'--working-directory='+SRC,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','python3','-c',remote]
(HERE/'launch.json').write_text(json.dumps({'unit':UNIT,'host':HOST,'argv':['systemd-run',*systemd[1:]],'fresh_remote_root':REMOTE,'capture_scope':'selected owned_primal::fold only, including transitive source dependencies; no source or harness edits','expected_phase':'initial Cargo compilation as needed, then one named Charon LLBC capture'},indent=2)+'\n')
with (HERE/'ssh-launch.log').open('w') as out:
 r=subprocess.run(['ssh',*SSH_OPTS,HOST,shlex.join(systemd)],stdout=out,stderr=subprocess.STDOUT)
(HERE/'launch-exit.txt').write_text(str(r.returncode)+'\n')
if r.returncode:
 print('systemd/remote capture failed; see ssh-launch.log',file=sys.stderr); sys.exit(r.returncode)
# Result retrieval; preserve remote result even on Charon failure by collecting logs first.
for name in ['capture-command.json','charon.stdout.log','charon.stderr.log','charon.time.log','result.json']:
 subprocess.run(['scp',*SSH_OPTS,f'{HOST}:{REMOTE}/{name}',str(HERE/name)],check=False)
res=json.loads((HERE/'result.json').read_text())
if res.get('llbc_exists'):
 subprocess.run(['scp',*SSH_OPTS,f'{HOST}:{REMOTE}/R664OwnedPrimalFold.llbc',str(HERE/'R664OwnedPrimalFold.llbc')],check=True)
(HERE/'capture-exit.txt').write_text(str(res.get('exit_status'))+'\n')
print(json.dumps(res,indent=2))
sys.exit(res.get('exit_status',1))
