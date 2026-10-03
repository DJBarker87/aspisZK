#!/usr/bin/env python3
"""Independent static/receipt audit of frozen R440 launch-a runner copies."""
import ast, hashlib, json, pathlib, re, sys
ROOT=pathlib.Path(__file__).resolve().parent
BASE=ROOT.parent
FROZEN=BASE/'lead-launch-a'
OUT=ROOT/'audit-report.json'
EXPECTED={
 'remote.py':'d5d343bb7837f7dbb8c737f6849a60469b9f98f6214950c88fd9845a67cf7ef4',
 'launch.py':'718bfd4932f0b0b32da180f66c68b6a3cb644cce548665508d6efe1c2d00d2fb',
}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def readj(p): return json.loads(p.read_text())
def check(ok,msg):
 if not ok: raise AssertionError(msg)
 return msg
checks=[]
for name,want in EXPECTED.items():
 p=FROZEN/name
 got=sha(p); check(got==want,f'{name} frozen SHA'); checks.append(f'{name} frozen SHA256 {got}')
 ast.parse(p.read_text(),filename=str(p)); checks.append(f'{name} parses as Python AST')
review=readj(FROZEN/'lead-review.json')
check(review['status']=='lead reviewed diagnostic launch approved','lead review status')
rev='3b9e8d7f0122e6dc966a809904adbd722ae3079d'
check(review['revision']==rev,'lead-reviewed source revision')
check(review['hashes']==EXPECTED,'lead review runner hashes')
check(review['exact_cli_differences']==[[0,'/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon','WRAPPER'],[44,'/home/dombarker/project-offloads/aspis-r437-pointer-wrapper-layout-20261003-a/R437PointerWrapperLayout.llbc','/home/dombarker/project-offloads/aspis-r440-actual-mono-closure-20261003-a/R440ActualMonoClosure.llbc']],'reviewed exact CLI delta')
checks.append('lead review pins exact two CLI differences at indices 0 and 44')
old=readj(pathlib.Path('.r21-scratch/r437-pointer-source-boundary/root-launch-a/saved-output/extract-command.json'))
new=readj(FROZEN/'saved-output/extract-command.json')
oldcmd=old['command']; newcmd=new['command']
check(len(oldcmd)==len(newcmd)==57,'CLI length')
normalized=list(oldcmd)
normalized[0]=newcmd[0]; normalized[44]=newcmd[44]
check(newcmd==normalized,'R440 command equals R437 except candidate wrapper and destination')
check([i for i,(a,b) in enumerate(zip(oldcmd,newcmd)) if a!=b]==[0,44],'computed exact changed argument positions')
check(new['base_extract_command_sha256']==old['base_extract_command_sha256']=='2bd178956b2fc4aaed055bc899349046f8969b238fa85bf027dd861becb2db96','base command identity')
check(newcmd[0]=='/home/dombarker/project-offloads/aspis-r440-mono-closure-binding-20261003-a/observer-bin/charon','candidate wrapper path')
check(newcmd[44]=='/home/dombarker/project-offloads/aspis-r440-actual-mono-closure-20261003-a/R440ActualMonoClosure.llbc','fresh R440 output path')
check(new['start_from']==['crate::freeze'] and old['start_from']==new['start_from'],'start root unchanged')
check(new['include']==old['include'] and len(new['include'])==16,'all 16 includes unchanged')
check(new['features']==old['features']=='insecure-spend-fixture,selected-v7-kernels','feature set unchanged')
check(new['monomorphize'] is True and old['monomorphize'] is True,'monomorphization retained')
check(newcmd[1:11]==['cargo','--preset','aeneas','--mir','built','--monomorphize','--sysroot','default','--start-from','crate::freeze'],'preset/MIR/monomorphization/sysroot/root')
check(newcmd[45:]==oldcmd[45:],'Cargo args unchanged')
check(newcmd[46:51]==['--offline','--locked','--release','--jobs','1'],'offline locked optimized one-job route')
check(newcmd[53:]==oldcmd[53:],'manifest and selected binary unchanged')
forbidden={'--print-original-ullbc','--skip-borrow-check','--no-borrow-check','--disable-borrow-check','--skip-typecheck','--no-typecheck','--skip-type-check','--no-type-check'}
check(not (forbidden & set(newcmd)),'no raw-MIR, borrow-check, or type-check bypass options')
checks.append('command reconstructed from frozen receipt; exact delta verified against R437')
remote=(FROZEN/'remote.py').read_text(); launch=(FROZEN/'launch.py').read_text()
for s in ["'--monomorphize'", "'--preset', 'aeneas'", "'--mir', 'built'", "'--sysroot', 'default'", "'--offline'", "'--locked'", "'--release'", "'--jobs', '1'", "'--features'", "'--start-from'", "'--include'", "'--dest-file'"]:
 check(s in remote,f'remote source contains {s}')
check("if os.environ.get('R440_ACTUAL_SOURCE_CAPTURE_ALLOW')!='1'" in remote and "if os.environ.get('R440_ACTUAL_SOURCE_CAPTURE_ALLOW') != '1'" in launch,'explicit capture gates')
check(f"'launch_revision':'{rev}'" in remote and f"LAUNCH_REVISION = '{rev}'" in launch,'launch revision gates')
check("assert not root.exists()" in remote,'remote fresh output root gate')
check("assert not (H / 'launch-status.json').exists() and not (H / 'saved-output').exists()" in launch,'local nonoverwrite gate')
check("RuntimeMaxSec=600s" in launch and "MemoryHigh=5G" in launch and "MemoryMax=7G" in launch and "MemorySwapMax=0" in launch and "TasksMax=128" in launch,'systemd caps and runtime')
check("--user', '--system" in remote or "('--user','--system')" in remote,'both user and system manager reservation census')
check('counted_cgroups=set()' in remote and 'if cgname not in counted_cgroups:' in remote,'deduplicated cgroup cap reservation')
check("'aspis-zk-site.service'" in remote or "name.startswith('aspis')" in remote,'site/aspis reservations included')
check("if pids:" in remote and "assert finite" in remote,'active uncapped Aspis jobs fail closed')
check("candidate_max+reserved_max<=safe" in remote,'aggregate reservation cap')
check("--systemd" not in remote,'') if False else None
checks.append('source statically retains capture, revision, fresh-output, resource, and reservation gates')
# Pins in frozen source and run receipts.
resdir=FROZEN/'saved-output'
result=readj(resdir/'result.json'); before=readj(resdir/'host-reservation-before.json'); after=readj(resdir/'host-reservation-after.json')
status=readj(FROZEN/'launch-status.json'); collection=readj(FROZEN/'collection-status.json')
check(status['ssh_exit_status']==0 and collection['exit_status']==0,'launch and collection status')
check(result['charon_exit_status']==0 and result['gnu_time_exit_status']==0 and result['wall_time']=='0:13.95' and result['peak_rss_kib']==630272 and result['swap_count']==0,'GNU time execution receipt')
check(result['llbc_exists'] and result['has_errors'] is False and result['formal_axioms'].startswith('N/A; diagnostic LLBC only'),'output exists, source translation has_errors false, no theorem axioms')
check(result['requested_root']=='crate::freeze' and result['capture_revision']==rev and result['source_revision_recorded']==rev,'captured root and revision')
check(result['llbc_sha256']=='01cd5ddc7086bba5f4e92802f90e59cce4034cf519d495ec35f925b91a6f033d','output hash')
check(result['original_driver_sha256']=='4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938' and result['candidate_driver_sha256']=='36cd66adb952d877a5ca6e17949fc4685525ed643d1b1fa7e92792d9a1d26625','original and candidate driver pins')
check(result['reviewed_patch_sha256']=='6208cbcd139815ed783ca83952fef7a539c89596156636c2ee7c283260ae9ad8','Bv2 patch pin')
check(result['candidate_overlay_hashes_before_after']['before']==result['candidate_overlay_hashes_before_after']['after']=={'main.rs':'afc8d62e3b0097805f9688653a0e435d54ea65c5c8ba3e698eb46a4fd16c49f5','translate_closures.rs':'93d29b0184be8503aafd8884f13f56eb73ea4f5eacdecb751bed5a28cc3fd5ed'},'candidate overlays stable')
check(result['source_hashes_before_after']['before']==result['source_hashes_before_after']['after'],'source hashes stable')
check(result['baseline_sha256_before_after']==['c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465']*2,'R429 comparison baseline stable')
check(result['r185_source_baseline_sha256_before_after']==['e8ee00cd440f7594e1a163290219c4e64a24141a722da6a861a45d0e61757e31']*2,'R185 source baseline stable')
check(result['r437_comparison_sha256_before_after']==['bafe9c1297a8ea92eaea3c37c685da3f5d3fe2e04c335ac9f1f4d64c4312386c']*2,'R437 comparison stable')
check(before['caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'recorded cgroup caps')
for o in [before,after]:
 cg=o['effective_cgroup_before'] if 'effective_cgroup_before' in o else o['effective_cgroup_after']
 check([cg[k] for k in ('memory.high','memory.max','memory.swap.max','pids.max')]==['5368709120','7516192768','0','128'],'actual cgroup controls')
 check(cg['memory.swap.current']=='0' and cg['memory.swap.peak']=='0','actual cgroup swap')
 ev=dict(line.split() for line in cg['memory.events'].splitlines())
 check(all(int(ev[k])==0 for k in ('high','max','oom','oom_kill','oom_group_kill')),'cgroup event counters')
check(before['active_aspis_units_both_managers']==[{'manager':'--system','unit':'aspis-zk-site.service','control_group':'/system.slice/aspis-zk-site.service','pids':['36883'],'MemoryMax_raw':'134217728','MemoryMax_bytes':134217728,'MemoryCurrent':'10661888'}],'captured additional capped Aspis service reservation')
check(before['deduplicated_reserved_memory_max_bytes']==134217728 and before['candidate_memory_max_bytes']==7516192768,'deduplicated reservation values')
check(before['safe_working_limit_bytes']==42949672960 and before['candidate_memory_max_bytes']+before['deduplicated_reserved_memory_max_bytes']<=before['safe_working_limit_bytes'],'aggregate safe limit')
check(before['launch_revision']==rev,'reservation launch revision')
check(before['wrapper_sha256']==before['original_wrapper_sha256']==before['original_driver_sha256'][:0]+ 'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c','wrapper pin')
check(after['candidate_wrapper_sha256_after']==after['original_wrapper_sha256_after']=='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c','wrapper unchanged after')
check(after['candidate_driver_sha256_after']==after['original_driver_sha256_after'][:0]+'36cd66adb952d877a5ca6e17949fc4685525ed643d1b1fa7e92792d9a1d26625','candidate driver unchanged after')
check(result['charon_toolchain']=='nightly-2026-06-01' and 'commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' in result['rustc_version_verbose'],'rust toolchain pin')
check(result['source_commit']=='cb50ff16b9f1066b8a97dc06da704de2da2fa41c','Charon source revision')
checks.append('captured run receipts, immutable source/tool pins, cgroup/swap/events, and output hash verified')
report={
 'status':'PASS', 'scope':'Independent static audit of frozen R440 runner copies plus their saved launch/extraction receipts.',
 'frozen_runner_sha256':EXPECTED, 'baseline_command':'R437 saved extraction command',
 'exact_cli_delta':[{'index':0,'change':'pinned original Charon wrapper to reviewed R440 candidate wrapper'},{'index':44,'change':'R437 destination to fresh R440 output destination'}],
 'command_properties':{'arguments':len(newcmd),'includes':len(new['include']),'start_from':new['start_from'],'features':new['features'],'monomorphize':new['monomorphize'],'rustflags_sha256':before['rustflags_sha256'],'preset':'aeneas','mir':'built','sysroot':'default','offline':True,'locked':True,'release':True,'jobs':1},
 'run':{'exit':result['charon_exit_status'],'wall_time':result['wall_time'],'peak_rss_kib':result['peak_rss_kib'],'swap_count':result['swap_count'],'llbc_sha256':result['llbc_sha256'],'has_errors':result['has_errors'],'cgroup_peak_bytes':after['effective_cgroup_after']['memory.peak'],'cgroup_swap_peak_bytes':after['effective_cgroup_after']['memory.swap.peak'],'cgroup_memory_events':after['effective_cgroup_after']['memory.events'],'reservation_before_bytes':before['deduplicated_reserved_memory_max_bytes'],'safe_working_limit_bytes':before['safe_working_limit_bytes'],'active_reservation_units':before['active_aspis_units_both_managers'],'source_hashes_before_after_equal':result['source_hashes_before_after']['before']==result['source_hashes_before_after']['after'],'stdlib_hashes_before_after_equal':before['stdlib_hashes_before']==after['stdlib_hashes_after']},
 'checks':checks,
 'boundary':'Runner/custody/resource and extraction-receipt audit only. The generated LLBC is a diagnostic native extraction; this audit establishes no source-to-model semantics, cryptographic property, probability statement, or release gate.',
}
OUT.write_text(json.dumps(report,indent=2)+'\n')
print('PASS',len(checks),'checks; report',OUT)
