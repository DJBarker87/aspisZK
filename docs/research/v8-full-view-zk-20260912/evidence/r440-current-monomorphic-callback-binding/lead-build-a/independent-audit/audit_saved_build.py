#!/usr/bin/env python3
"""Independent read-only checks over saved R440 clone/build/fixture receipts."""
import hashlib, json, re, sys
from pathlib import Path
ROOT=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
BASE=ROOT/'.r21-scratch/r440-mono-closure-binding'
RUN=BASE/'lead-build-a'
FIX=BASE/'fixture/candidate-saved'
errors=[]; checks=[]
def load(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def ck(cond,label,detail=None):
 if cond: checks.append(label)
 else: errors.append({'check':label,'detail':detail})
clone=load(RUN/'clone-saved/clone-audit.json'); tree=load(RUN/'clone-saved/tracked-tree.json')
pins=load(RUN/'r440-candidate-b-pins.json'); approval=load(RUN/'lead-compile-approval.json')
sel=load(RUN/'build-saved/direct-input-selection.json'); cmd=load(RUN/'build-saved/direct-command.json'); result=load(RUN/'build-saved/direct-result.json')
fixture_cmd=load(FIX/'command.json'); fixture_res=load(FIX/'result.json')
# Clone custody: source revision, exact overlay set, tracked row set and archive state.
expected_paths=['charon/src/bin/charon-driver/main.rs','charon/src/bin/charon-driver/translate/translate_closures.rs']
tracked_hashes=clone.get('tracked_source_sha256_before',{})
candidate_hashes=clone.get('tracked_candidate_sha256_after_overlay',{})
changed=sorted(k for k in tracked_hashes.keys()|candidate_hashes.keys() if tracked_hashes.get(k)!=candidate_hashes.get(k))
ck(load(RUN/'clone-launch-status.json')['exit_status']==0 and load(RUN/'clone-stage-status.json')['exit_status']==0 and load(RUN/'clone-collection.json')['exit_status']==0,'clone launch, staging, and collection statuses are successful')
ck(load(RUN/'build-launch-status.json')['exit_status']==0 and load(RUN/'build-stage-status.json')['exit_status']==0 and load(RUN/'build-collection.json')['exit_status']==0,'build launch, staging, and collection statuses are successful')
ck(clone['source_head']=='cb50ff16b9f1066b8a97dc06da704de2da2fa41c','clone pinned source HEAD',clone.get('source_head'))
ck(clone['campaign_revision']=='3b9e8d7f0122e6dc966a809904adbd722ae3079d','clone campaign revision',clone.get('campaign_revision'))
ck(clone['tracked_entry_count']==1169 and len(tree)==1169 and len(tracked_hashes)==1169 and len(candidate_hashes)==1169,'clone tracked inventory has 1169 exact entries',{'tree':len(tree),'source':len(tracked_hashes),'candidate':len(candidate_hashes)})
ck(sorted(clone['tracked_symlink_paths'])==['doc-ml.html','doc-rust.html','rust-toolchain'],'clone tracked symlinks recorded',clone.get('tracked_symlink_paths'))
ck(changed==expected_paths and clone['only_tracked_source_differences']==expected_paths,'clone has exactly the two approved driver source deltas',{'derived':changed,'receipt':clone['only_tracked_source_differences']})
ck(clone['candidate_target_cache_absent'] is True and clone['target_cache_copied'] is False,'clone is source-only without copied target cache')
ck(clone['shared_regular_source_inode_count']==0,'clone has zero shared regular source inodes')
ck(pins['status']=='reviewed-candidate-b-pins' and clone['candidate_b_pins_sha256']==sha(RUN/'r440-candidate-b-pins.json'),'reviewed candidate pins match clone receipt')
ck(pins['candidate_json_sha256']=='1f56c9961928ad68ee787d41147bbeed91ec2acacaa45de9aade66e6b74db86d' and pins['patch_sha256']=='6208cbcd139815ed783ca83952fef7a539c89596156636c2ee7c283260ae9ad8','candidate Bv2 metadata and patch pins match')
ck(approval['clone_audit_sha256']==sha(RUN/'clone-saved/clone-audit.json'),'compile approval references exact saved clone audit')
for key,expected in [('memory.high','5368709120'),('memory.max','7516192768'),('memory.swap.max','0'),('pids.max','128')]:
 ck(clone['effective_cgroup_before'].get(key)==expected,'clone cgroup '+key,clone['effective_cgroup_before'].get(key))
ck(clone['other_aspis_reserved_max_bytes']==134217728 and any(x['unit']=='aspis-zk-site.service' and x['MemoryMax_bytes']==134217728 for x in clone['other_aspis_units']),'clone reservation includes capped system site service')
# Build custody and selected inputs.
ck(cmd['source_revision']=='cb50ff16b9f1066b8a97dc06da704de2da2fa41c' and cmd['campaign_source_revision']==clone['campaign_revision'],'direct build source/campaign revisions')
ck(sel['dependency_count']==46 and len(sel['selected_externs'])==46 and len({x['name'] for x in sel['selected_externs']})==46,'direct build uses 46 uniquely named pinned externs')
ck(len(sel['native_build_output_entries'])==2 and [x['path'] for x in sel['native_build_output_entries']]==['release/build/psm-0054b740d3e1ad34/out/4f9a91766097c4c5-x86_64.o','release/build/psm-0054b740d3e1ad34/out/libpsm_s.a'],'two PSM native inputs explicitly pinned')
ck(cmd['candidate_b_json_sha256']==pins['candidate_json_sha256'] and cmd['candidate_b_patch_sha256']==pins['patch_sha256'] and cmd['candidate_b_pin_manifest_sha256']==sha(RUN/'r440-candidate-b-pins.json'),'build pins agree with reviewed clone pins')
ck(cmd['overlay_pins']==pins['overlays'],'build overlay pins agree with candidate B manifest')
ck(cmd['inputs_before']==result['inputs_before'] and result['inputs_before']==result['inputs_after'] and result['inputs_unchanged'] is True,'all recorded tracked source and selected cache inputs unchanged across build')
ck(result['parent_git_before']==result['parent_git_after'] and result['parent_git_after']['head']==cmd['source_revision'] and result['parent_git_after']['porcelain']=='','pinned parent checkout stayed clean and unchanged')
ck(result['candidate_b_pin_manifest_sha256']==sha(RUN/'r440-candidate-b-pins.json'),'compiled worker pin manifest hash matches saved reviewed manifest')
# Independently cross-check cache manifests, extern argv, and native rows.
before=cmd['inputs_before'];deps=before['release_deps_sha256']
ck(deps['expected_count']==deps['actual_count'] and deps['expected_sha256']==deps['observed_sha256'],'read-only release dependency cache matches expected complete inventory',{'counts':[deps['expected_count'],deps['actual_count']]})
ck(all(deps['expected_sha256'].get(x['path'].removeprefix('charon/target/'))==x['sha256'] for x in sel['selected_externs']),'all 46 selected extern hashes occur in the pinned dependency-cache inventory')
ck(before['parent_tracked_source_sha256']==clone['tracked_source_sha256_before'] and before['candidate_tracked_source_sha256']==clone['tracked_candidate_sha256_after_overlay'],'build source snapshots match independent clone audit')
argv=cmd['command'];externs={}
for i,arg in enumerate(argv[:-1]):
 if arg=='--extern':
  name,path=argv[i+1].split('=',1);externs[name]=path
expected_externs={x['name']:'/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/'+x['path'] for x in sel['selected_externs']}
ck(externs==expected_externs,'rustc command extern bindings equal selected 46 input manifest',{'actual_count':len(externs),'expected_count':len(expected_externs)})
ck(before['native']==[{'name':x['path'],'relative_path':x['path'],'sha256':x['sha256'],'size':x['size']} for x in sel['native_build_output_entries']],'native input source/hash/size rows match selection')
for key,expected in [('memory.high','5368709120'),('memory.max','7516192768'),('memory.swap.max','0'),('pids.max','128')]:
 ck(cmd['effective_cgroup_before'].get(key)==expected and result['cgroup_after'].get(key)==expected,'direct build cgroup '+key)
ck(result['rustc_exit_status']==0 and result['gnu_time_exit_status']==0 and result['target_exists'] is True,'direct rustc target exit status and output exist')
ck(result['driver_sha256']=='36cd66adb952d877a5ca6e17949fc4685525ed643d1b1fa7e92792d9a1d26625','direct rustc driver output SHA matches reported artifact')
ck(result['gnu_time_elapsed']=='0:13.54' and result['gnu_time_peak_rss_kib']==1569908 and result['gnu_time_swaps']==0,'GNU time metrics match reported successful build')
ck(result['cgroup_after']['memory.peak']=='1828773888' and result['cgroup_after']['memory.swap.current']=='0','cgroup peak/swap metrics match successful build')
events=result['cgroup_after']['memory.events'];ck(all(int(dict(line.split() for line in events.splitlines()).get(k,'0'))==0 for k in ('oom','oom_kill','oom_group_kill')) and result['oom_detected'] is False,'direct build has no OOM events')
gnu=(RUN/'build-saved/rustc-gnu-time.txt').read_text()
ck(bool(re.search(r'Maximum resident set size \(kbytes\):\s*1569908',gnu)) and bool(re.search(r'Swaps:\s*0',gnu)) and bool(re.search(r'Exit status:\s*0',gnu)),'raw GNU time output agrees with parsed metrics')
ck((RUN/'build-saved/rustc.stdout.log').is_file() and (RUN/'build-saved/rustc.stdout.log').stat().st_size==0,'successful rustc stdout/stderr capture exists and is empty')
# Focused actual fixture: this is a diagnostic translation fixture, not source proof.
ck(fixture_res['exit_status']==0 and fixture_res['target_exists'] is True and fixture_res['has_errors'] is False,'candidate native fixture translation succeeded')
ck(fixture_cmd['driver_sha256']==result['driver_sha256'] and fixture_res['target_sha256']==hashlib.sha256((FIX/'baseline.llbc').read_bytes()).hexdigest(),'fixture used the audited driver and saved LLBC hash matches receipt')
ck(fixture_cmd['candidate_overlay_sha256']=={'main':pins['overlays'][0]['candidate_sha256'],'translate_closures':pins['overlays'][1]['candidate_sha256']},'fixture input candidate overlay pins match build')
ck(fixture_res['wall_time']=='0:00.07' and fixture_res['peak_rss_kib']==115808 and fixture_res['swaps']==0,'fixture metrics match receipt')
ck(fixture_res['effective_cgroup_after']['memory.high']=='5368709120' and fixture_res['effective_cgroup_after']['memory.max']=='7516192768' and fixture_res['effective_cgroup_after']['memory.swap.max']=='0' and fixture_res['effective_cgroup_after']['pids.max']=='128' and fixture_res['effective_cgroup_after']['memory.peak']=='396587008','fixture cgroup cap/peak/swap match receipt')
ck(fixture_cmd['formal_axioms']=='N/A diagnostic extraction','fixture correctly records formal axioms as not applicable')
report={'status':'PASS' if not errors else 'FAIL','classification':'read-only independent saved-receipt/source-custody audit; no build rerun','checks_passed':len(checks),'checks':checks,'errors':errors,'clone':{'tracked_entries':clone['tracked_entry_count'],'allowed_changes':clone['only_tracked_source_differences'],'target_cache_copied':clone['target_cache_copied'],'shared_regular_inodes':clone['shared_regular_source_inode_count'],'other_reserved_max_bytes':clone['other_aspis_reserved_max_bytes'],'site_service_memory_max':134217728},'build':{'exit_status':result['rustc_exit_status'],'driver_sha256':result['driver_sha256'],'wall':result['gnu_time_elapsed'],'rss_kib':result['gnu_time_peak_rss_kib'],'swap_count':result['gnu_time_swaps'],'cgroup_peak_bytes':result['cgroup_after']['memory.peak'],'oom':result['oom_detected'],'input_hashes_unchanged':result['inputs_unchanged'],'extern_count':sel['dependency_count']},'fixture':{'exit_status':fixture_res['exit_status'],'llbc_sha256':sha(FIX/'baseline.llbc'),'wall':fixture_res['wall_time'],'rss_kib':fixture_res['peak_rss_kib'],'swap_count':fixture_res['swaps'],'has_errors':fixture_res['has_errors'],'axioms':'N/A diagnostic extraction'},'boundary':'Diagnostic tool compilation and one native fixture capture only. This audit makes no claim of general source semantics, proof closure, Rust correspondence, or release/security adequacy.'}
out=RUN/'independent-audit/audit-report.json';out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2));sys.exit(bool(errors))
