#!/usr/bin/env python3
"""Read-only consistency audit for saved R429 actual freeze fold capture C."""
import hashlib, json, re
from pathlib import Path

CAP=Path(__file__).resolve().parents[1]
FOLD=CAP.parent
OUT=CAP/'saved-output'
checks=[]
def load(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check(ok,label,details=None):
    checks.append({'check':label,'ok':bool(ok),'details':details})
    if not ok: raise AssertionError(f'{label}: {details!r}')

plan=load(CAP/'planned-command.json')
receipt=load(CAP/'changed-scope-receipt.json')
result=load(OUT/'result.json')
command=load(OUT/'extract-command.json')
runner=load(OUT/'runner-status.json')
before=load(OUT/'host-reservation-before.json')
after=load(OUT/'host-reservation-after.json')
llbc_path=OUT/'R429ActualFreezeFold.llbc'
stdout=OUT/'charon.stdout.log'; stderr=OUT/'charon.stderr.log'; gnu=OUT/'gnu-time.txt'

# Artifact bytes, status, and resource metrics.
for label,path,key,bytes_key in [('LLBC',llbc_path,'llbc_sha256',None),('stdout',stdout,'charon_stdout_sha256','charon_stdout_bytes'),('stderr',stderr,'charon_stderr_sha256','charon_stderr_bytes')]:
    actual=sha(path); check(actual==result[key],f'{label} hash matches result',{'actual':actual,'recorded':result[key]})
    if bytes_key: check(path.stat().st_size==result[bytes_key],f'{label} length matches result',{'actual':path.stat().st_size,'recorded':result[bytes_key]})
time=gnu.read_text()
wm=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)',time)
rm=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',time)
sm=re.search(r'Swaps:\s*(\d+)',time)
em=re.search(r'Exit status:\s*(\d+)',time)
check(all((wm,rm,sm,em)),'GNU-time metric fields present')
check(wm.group(1)==result['wall_time']=='0:14.49','wall metric agrees',wm.group(1))
check(int(rm.group(1))==result['peak_rss_kib']==630092,'RSS metric agrees',rm.group(1))
check(int(sm.group(1))==result['swap_count']==0,'swap metric agrees and zero',sm.group(1))
check(int(em.group(1))==result['gnu_time_exit_status']==result['charon_exit_status']==0,'exit metrics agree and success')
check(runner['status']=='terminal' and runner['code']==0,'runner status terminal success')
check(result['has_errors'] is False and result['llbc_exists'] is True,'result records error-free LLBC')
check(result['formal_axioms']=='N/A; diagnostic LLBC only','axiom status is N/A for extraction')

# Exact command delta from R185 and from successful attempt B.
new=command['command']; planned=plan['command']
check(new==planned,'executed command equals reviewed plan')
base=load(CAP/'base-extract-command.snapshot.json')
check(sha(CAP/'base-extract-command.snapshot.json')==plan['base_extract_command_sha256'],'base command snapshot hash matches plan')
check(sha(CAP/'base-extract-command.snapshot.json')=='2bd178956b2fc4aaed055bc899349046f8969b238fa85bf027dd861becb2db96','base command has expected pinned hash')
base_cmd=base['command']
delta=[('core::slice::iter::_::fold'),('core::slice::iter::Iter'),('core::mem::SizedTypeProperties::IS_ZST'),('core::mem::SizedTypeProperties::SIZE')]
def remove_pairs(xs,pairs):
    out=[]; i=0; seen=[]
    while i<len(xs):
        if i+1<len(xs) and xs[i]=='--include' and xs[i+1] in pairs:
            seen.append(xs[i+1]); i+=2
        else: out.append(xs[i]); i+=1
    return out,seen
def normalize_dest(xs):
    ys=list(xs); j=ys.index('--dest-file'); ys[j+1]='<DEST>'
    return ys
stripped,seen=remove_pairs(new,delta)
check(seen==delta and len(seen)==4,'only the four planned include pairs occur',seen)
check(normalize_dest(stripped)==normalize_dest(base_cmd),'command is R185 base plus four includes and destination change',{'delta':seen,'base_dest':base_cmd[base_cmd.index('--dest-file')+1],'new_dest':new[new.index('--dest-file')+1]})
check(plan['only_scope_delta']==delta,'plan records exact four-include delta',plan['only_scope_delta'])
check(plan['base_llbc_sha256']=='e8ee00cd440f7594e1a163290219c4e64a24141a722da6a861a45d0e61757e31' and result['baseline_sha256_before_after']==[plan['base_llbc_sha256']]*2,'base R185 LLBC pins stable')
# C adds only SIZE relative to successful B.
bdir=FOLD/'root-launch-b'
bres=load(bdir/'saved-output/result.json')
bcmd=load(bdir/'saved-output/extract-command.json')['command']
check(receipt['previous_status'].startswith('success') and receipt['previous_output_sha256']==bres['llbc_sha256']=='3eb71115ebd990e246f79657d48c8067f52541dd406d150a76d60add7bc020af','changed-scope receipt pins successful B output')
check(receipt['new_remote_script_sha256']==load(CAP/'launch-status.json')['remote_script_sha256'],'changed scope script hash matches launch receipt')
b_delta=['core::mem::SizedTypeProperties::SIZE']
c_without_size,seen_size=remove_pairs(new,b_delta)
check(seen_size==b_delta,'C adds exactly SIZE relative to B',seen_size)
check(normalize_dest(c_without_size)==normalize_dest(bcmd),'C command reduces to B command after removing SIZE/dest delta')

# Input source/Cargo/std pins unchanged before and after; includes callback pin.
expected_sources={'r110_norm.rs':'8459fc12322811b589f9a9d29bf474f3ee45e58aa13c716b8f324c2db81b160e','circle_norm.rs':'3f0882366674d5d41e365e62787d85b62076e6077697e9f756e135ce12aedbd2','line_norm.rs':'4fb70d37d16053a74e08716433af45998e7ddd13fc5dca7b1c86505ed7e2c528','joined_inverse.rs':'ef9b45ce8a7ffbcf57564bcc1348cae3197a09fbbbd529ffca632b778281efeb','aspis_core_field.rs':'639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499','performance_host_Cargo.toml':'62f81cd54314ec1a637c61404bd6cf6f12f8defbf1ab68fb0ded4956df80646c','performance_host_Cargo.lock':'a2e3d525c3a0f01428b56df55001ba304981a6b8c26cca08badf7b09b7029814','relation_callback.rs':'4f8f80e0847ec004a56fc693f6096308090de5f3cbed35722dba330afaa9820f'}
check(before['source_hashes_before']==after['source_hashes_after']==expected_sources,'eight source/Cargo/callback pins match and stable')
check(result['source_hashes_before_after']['before']==result['source_hashes_before_after']['after']==expected_sources,'result source hashes match')
expected_std={'/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/slice/iter/macros.rs':'0ac47d295999ba8847d0df93557292fbad65d256db0c6521c396798d2e37677d','/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/slice/iter.rs':'83205f82241154964b1aecef87913ec92ce8c0b99285337c04e37840594f9251','/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/ptr/non_null.rs':'adba64467653633cfa3fe0bbe6eec6f6d723221396b529c92d51eb9e39ba8cdd','/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/mem/mod.rs':'9f450467849a7e829d2f57fe826518b7334df8a8eb206052d571ad7b5d018b9e'}
check(before['stdlib_hashes_before']==after['stdlib_hashes_after']==expected_std,'four monitored standard-library source pins match and stable')
check(result['source_revision_recorded']==result['capture_revision']==load(CAP/'launch-status.json')['launch_revision']=='956b16b46251cc24f0883a17114695ffbb960510','launch/source revision receipts agree')
check(result['source_commit']=='cb50ff16b9f1066b8a97dc06da704de2da2fa41c','Charon source revision recorded')
check('commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' in result['rustc_version_verbose'],'pinned rustc version receipt')

# Actual limits/events and reservation include active 128 MiB website service.
for label,cg in [('before',before['effective_cgroup_before']),('runner',runner['effective_cgroup']),('after',after['effective_cgroup_after'])]:
    caps=(cg['memory.high'],cg['memory.max'],cg['memory.swap.max'],cg['pids.max'])
    check(caps==('5368709120','7516192768','0','128'),f'{label} effective cgroup caps',caps)
check(runner['effective_cgroup']['memory.events']=='low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0','cgroup memory events clean')
check(runner['effective_cgroup']['memory.swap.current']=='0' and runner['effective_cgroup']['memory.swap.peak']=='0','cgroup swap usage zero')
check(int(runner['effective_cgroup']['memory.peak'])<7516192768,'cgroup peak below max',runner['effective_cgroup']['memory.peak'])
check(before['caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'requested caps explicit',before['caps'])
website=next((x for x in before['system_reservations'] if 'aspis-zk-site.service' in x['unit']),None)
check(website is not None and website['MemoryMax']=='134217728','website service reservation recorded at 128 MiB',website)
check(before['system_reserved_memory_max_bytes']==134217728,'recorded reserved service cap equals 128 MiB')
check(before['existing_aspis_slices']==[] and before['other_active_aspis_services']==[] and before['heavy_processes']==[],'no competing Aspis build reservation/process')
check(before['active_slice_memory_max_bytes']+before['system_reserved_memory_max_bytes']+before['candidate_memory_max_bytes']<=before['safe_working_limit_bytes'],'host reservation below safe working limit',{'sum':before['active_slice_memory_max_bytes']+before['system_reserved_memory_max_bytes']+before['candidate_memory_max_bytes'],'limit':before['safe_working_limit_bytes']})

# Preserve the failed A preflight and successful B predecessor.
adir=FOLD/'root-launch'; astatus=load(adir/'launch-status.json'); acoll=load(adir/'collection-status.json')
check(astatus['ssh_exit_status']==1 and acoll['exit_status']==0,'attempt A preflight failure and collected history remain present',{'launch':astatus,'collection':acoll})
check((adir/'ssh-launch.log').exists() and (adir/'collection.stderr.log').exists() and not (adir/'saved-output/result.json').exists(),'attempt A raw history retained without falsely treating it as a run')
check(bres['charon_exit_status']==0 and bres['llbc_exists'] and bres['has_errors'] is False,'attempt B successful output retained')
check((bdir/'saved-output/gnu-time.txt').exists() and (bdir/'saved-output/charon.stderr.log').exists(),'attempt B logs retained')

# LLBC exact declaration identities/body opacity requested by root.
llbc=load(llbc_path); t=llbc['translated']
check(llbc['has_errors'] is False,'decoded LLBC has_errors false')
def decl(kind,n): return next(x for x in t[kind] if x and x['def_id']==n)
def id_names(x): return [part['Ident'][0] for part in x['item_meta']['name'] if 'Ident' in part]
fun70=decl('fun_decls',70); type42=decl('type_decls',42); global31=decl('global_decls',31); global32=decl('global_decls',32); fun142=decl('fun_decls',142); fun145=decl('fun_decls',145); fun153=decl('fun_decls',153)
check(id_names(fun70)[-1]=='fold' and fun70['item_meta']['opacity']=='Transparent' and fun70['body'] is not None,'Fun70 fold has transparent emitted body',{'name':id_names(fun70),'opacity':fun70['item_meta']['opacity'],'body':fun70['body'] is not None})
check(fun70['body']['Structured']['span']['data']['beg']['line']==259 and fun70['body']['Structured']['span']['data']['end']['line']==289,'Fun70 span matches fold source lines')
check(id_names(type42)[-1]=='Iter' and type42['item_meta']['opacity']=='Transparent' and type42['kind'].get('Struct') is not None,'Type42 Iter is transparent struct',{'name':id_names(type42),'opacity':type42['item_meta']['opacity'],'kind':list(type42['kind'])})
for g,num,member,initializer in [(global31,31,'IS_ZST',142),(global32,32,'SIZE',145)]:
    check(id_names(g)[-1]==member and g['item_meta']['opacity']=='Transparent','Global'+str(num)+' '+member+' transparent',{'name':id_names(g),'opacity':g['item_meta']['opacity']})
    call=g['value']['kind'].get('Call',[])
    target=call[0]['kind']['Fun']['Regular'] if call else None
    check(target==initializer,'Global'+str(num)+' initializer targets Fun'+str(initializer),target)
check(id_names(fun142)[-1]=='IS_ZST' and fun142['item_meta']['opacity']=='Transparent' and fun142['body'] is not None,'Fun142 IS_ZST initializer transparent')
check(fun142['body']['Structured']['span']['data']['beg']['line']==1420,'Fun142 source line recorded')
check(id_names(fun145)[-1]=='SIZE' and fun145['item_meta']['opacity']=='Transparent' and fun145['body'] is not None,'Fun145 SIZE initializer transparent')
check(fun145['body']['Structured']['span']['data']['beg']['line']==1379,'Fun145 source line recorded')
check(id_names(fun153)[-1]=='size_of' and fun153['item_meta']['opacity']=='Foreign' and fun153['body'].get('Intrinsic',{}).get('name')=='size_of','Fun153 is Foreign size_of intrinsic',{'name':id_names(fun153),'opacity':fun153['item_meta']['opacity'],'body':fun153['body']})

report={'status':'PASS' if all(x['ok'] for x in checks) else 'FAIL','classification':'read-only consistency audit of saved R429 capture C; no extraction/build/proof or Rust source-semantics claim','checks':checks,'summary':{'llbc_sha256':result['llbc_sha256'],'charon_exit':result['charon_exit_status'],'wall_time':result['wall_time'],'peak_rss_kib':result['peak_rss_kib'],'swap_count':result['swap_count'],'has_errors':llbc['has_errors'],'Fun70':'Transparent body','Type42':'Transparent Iter struct','Global31/32':'Transparent IS_ZST/SIZE initializers','Fun153':'Foreign size_of intrinsic','formal_axioms':'N/A'},'artifacts':{str(p.relative_to(CAP)):sha(p) for p in [llbc_path,stdout,stderr,gnu,OUT/'result.json',OUT/'extract-command.json',OUT/'runner-status.json',OUT/'host-reservation-before.json',OUT/'host-reservation-after.json',CAP/'planned-command.json',CAP/'base-extract-command.snapshot.json',CAP/'changed-scope-receipt.json']},'scope_note':'Verifies saved bytes, command/receipt metrics, pins, resource receipt and LLBC declaration metadata only. It does not claim that the body was executed, that source comments establish correctness, that any pointer/aliasing property holds, or that a Rust-to-Lean correspondence is proved.'}
(CAP/'independent-capture-audit'/'audit-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'check_count':len(checks),'failed':[c for c in checks if not c['ok']],'report':str(CAP/'independent-capture-audit'/'audit-report.json')},indent=2))
