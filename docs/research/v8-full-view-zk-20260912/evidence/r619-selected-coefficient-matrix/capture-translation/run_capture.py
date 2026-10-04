#!/usr/bin/env python3
"""One authorized generic/default-const R618 r83_matrix capture; no source edits."""
import hashlib,json,pathlib,subprocess,shlex,sys
HERE=pathlib.Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'; OPTS=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
SSH=['ssh',*OPTS]; SCP=['scp',*OPTS]
REMOTE='/home/dombarker/project-offloads/aspis-r618-matrix-generic-20261004-a'
UNIT='aspis-r618-matrix-generic-20261004-a'
SRC='/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
CHARON='/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon'
CHARON_SHA='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
PINS={'query_arithmetic.rs':'545e1dac8421bfd2bc2635590d0d6e1065a58c0f02924f25c8228f44d0a3590d','r17_host_relation.rs':'3b7a5040509e0c3ad5e421e49a4f6d1d106c5adabfc2bf891bf8685c66b4b801','relation_callback.rs':'4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f','performance_host_Cargo.toml':'62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c','performance_host_Cargo.lock':'a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814','field.rs':'639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499'}
PATHS={'query_arithmetic.rs':SRC+'/docs/research/v8-no-work-100-20260907/experiments/query_arithmetic.rs','r17_host_relation.rs':SRC+'/docs/research/v8-no-work-100-20260907/experiments/r17_host_relation.rs','relation_callback.rs':SRC+'/docs/research/v8-no-work-100-20260907/experiments/relation_callback.rs','performance_host_Cargo.toml':SRC+'/docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml','performance_host_Cargo.lock':SRC+'/docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.lock','field.rs':SRC+'/crates/aspis-core/src/field.rs'}
FLAGS=['--cfg','v8_positive_transfer','--cfg','v8_complete','--cfg','v8_performance_fast','--cfg','v8_structured','--cfg','v8_fine_profile','--cfg','v8_batch_m','--cfg','v8_tower_batch','--cfg','v8_query_kernels','--cfg','v8_fused_rows','--cfg','v8_shared_weights','--cfg','v8_block_horner','--cfg','v8_gamma_wrap','--cfg','v8_reuse_gamma','--cfg','v8_grouped_linear','--cfg','v8_query_shared','--cfg','v8_range_m31','--cfg','v8_range_cm31','--cfg','v8_sparse_groups','--cfg','v8_range_dots','--cfg','v8_cm_schoolbook','--cfg','v8_prepared_schoolbook','--cfg','v8_quiet_profile','--cfg','v8_payment_extraction','--cfg','v8_performance','--cfg','v8_qm_hybrid','--cfg','v8_qm_lazy_c0','--cfg','v8_gamma_partial','-A','dead_code','-A','unexpected_cfgs','--cfg','v8_circle_norm','--cfg','v8_chord_norm','--cfg','v8_joined_inverse','--cfg','v8_split_inverse','--cfg','v8_line_norm','--cfg','v8_quotient_fused','--cfg','v8_affine_primal','--cfg','v8_compact_workspace','--cfg','v8_gamma_fixed','--cfg','v8_merkle_slices','--cfg','v8_merkle_borrow','--cfg','v8_leaf_record']
FLAGS_SHA='f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613'
cmd=[CHARON,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::query_arithmetic::r83_matrix','--include','aspis_core::field','--dest-file',REMOTE+'/R618MatrixGeneric.llbc','--','--offline','--locked','--release','--jobs','1','--features','insecure-spend-fixture,selected-v7-kernels','--manifest-path',PATHS['performance_host_Cargo.toml'],'--bin','aspis-v8-performance-host']
remote=r'''import hashlib,json,pathlib,re,subprocess,sys
root=pathlib.Path(@REMOTE@); charon=pathlib.Path(@CHARON@)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not root.exists(),root
assert sha(charon)==@CHARON_SHA@
paths=@PATHS@; pins=@PINS@
assert {k:sha(pathlib.Path(v)) for k,v in paths.items()}==pins
assert hashlib.sha256(json.dumps(@FLAGS@,separators=(',',':')).encode()).hexdigest()==@FLAGS_SHA@
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'128'},limits
units=subprocess.check_output(['systemctl','--user','list-units','--type=service','--state=running','--plain','--no-legend'],text=True); reservations=[]
for line in units.splitlines():
 w=line.split()
 if w and w[0].startswith('aspis'):
  v=subprocess.check_output(['systemctl','--user','show',w[0],'-p','MemoryMax'],text=True).strip().split('=',1)[1]
  if v.isdigit():reservations.append((w[0],int(v)))
assert sum(v for _,v in reservations)<=40*1024**3,reservations
root.mkdir(mode=0o700)
cmd=@CMD@
env=dict(**__import__('os').environ);env['PATH']='/home/dombarker/.cargo/bin:/home/dombarker/.elan/bin:'+env.get('PATH','');env['RUSTFLAGS']=' '.join(@FLAGS@);env['CARGO_INCREMENTAL']='0'
(root/'capture-command.json').write_text(json.dumps({'target':'R618 generic/default-const selected r83_matrix capture','argv':cmd,'command_difference_from_predecessor':{'removed':['--monomorphize','--consts values','--include core::result'],'retained':['--start-from crate::query_arithmetic::r83_matrix','--include aspis_core::field','measured R117 Rust flags']},'charon_sha256':@CHARON_SHA@,'source_hashes':pins,'rustflags':@FLAGS@,'rustflags_sha256':@FLAGS_SHA@,'caps':limits,'reservations':reservations},indent=2)+'\n')
with (root/'charon.stdout.log').open('w') as out, (root/'charon.stderr.log').open('w') as err: r=subprocess.run(['/usr/bin/time','-v','-o',str(root/'charon.time.log'),*cmd],stdout=out,stderr=err,env=env)
llbc=root/'R618MatrixGeneric.llbc'
result={'exit_status':r.returncode,'llbc_exists':llbc.exists(),'charon_sha256':@CHARON_SHA@,'formal_axioms':'N/A; capture only'}
if llbc.exists():
 result['llbc_sha256']=sha(llbc);result['llbc_bytes']=llbc.stat().st_size
 try:
  d=json.loads(llbc.read_text());result['has_errors']=d.get('has_errors');tr=d.get('translated',{});result['counts']={k:len(tr.get(k,[])) for k in ['fun_decls','type_decls','global_decls','trait_decls','trait_impls','ordered_decls']}
 except Exception as e: result['llbc_parse_error']=repr(e)
(root/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));sys.exit(r.returncode)
'''
rep={'REMOTE':REMOTE,'CHARON':CHARON,'CHARON_SHA':CHARON_SHA,'PATHS':PATHS,'PINS':PINS,'FLAGS':FLAGS,'FLAGS_SHA':FLAGS_SHA,'CMD':cmd}
for k,v in rep.items():remote=remote.replace('@'+k+'@',repr(v))
systemd=['systemd-run','--user','--wait','--collect','--pipe','--unit='+UNIT,'--working-directory='+SRC,'-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s','python3','-c',remote]
(HERE/'R618-generic-launch.json').write_text(json.dumps({'unit':UNIT,'argv':systemd,'fresh_remote_root':REMOTE,'kind':'one changed generic/default-const capture; no source edits'},indent=2)+'\n')
with (HERE/'R618-generic-ssh.log').open('w') as out:r=subprocess.run([*SSH,HOST,shlex.join(systemd)],stdout=out,stderr=subprocess.STDOUT)
(HERE/'R618-generic-launch-exit.txt').write_text(str(r.returncode)+'\n')
for n in ['capture-command.json','charon.stdout.log','charon.stderr.log','charon.time.log','result.json']:
 subprocess.run([*SCP,f'{HOST}:{REMOTE}/{n}',str(HERE/('R618-generic-'+n))],check=False)
if r.returncode:sys.exit(r.returncode)
subprocess.run([*SCP,f'{HOST}:{REMOTE}/R618MatrixGeneric.llbc',str(HERE/'R618MatrixGeneric.llbc')],check=True)
