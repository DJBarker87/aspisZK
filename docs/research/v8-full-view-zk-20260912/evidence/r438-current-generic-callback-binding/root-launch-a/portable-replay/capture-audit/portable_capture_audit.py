#!/usr/bin/env python3
"""Portable replay of the preserved R438 custody audit."""
#!/usr/bin/env python3
"""Read-only independent custody/checksum/command-delta audit of saved R438."""
from pathlib import Path
import hashlib,json,re,sys
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
OUT=BASE/'saved-output'
PREV=BASE/'baseline-r437'
def readj(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
def ck(name,ok,detail=None):
 checks.append({'check':name,'pass':bool(ok),'detail':detail})
 if not ok: raise SystemExit(f'FAIL {name}: {detail}')
launch=readj(BASE/'launch-status.json'); collection=readj(BASE/'collection-status.json')
argv=readj(BASE/'ssh-argv.json'); plan=readj(BASE/'candidate-plan.json')
result=readj(OUT/'result.json'); command=readj(OUT/'extract-command.json')
before=readj(OUT/'host-reservation-before.json'); after=readj(OUT/'host-reservation-after.json')
llbc=OUT/'R438GenericClosureDispatch.llbc'; so=OUT/'charon.stdout.log'; se=OUT/'charon.stderr.log'; gt=(OUT/'gnu-time.txt').read_text()
old=readj(PREV/'extract-command.json')['command']; new=command['command']
old_norm=[x for x in old if x!='--monomorphize']; di=old_norm.index('--dest-file'); old_norm[di+1]=new[new.index('--dest-file')+1]
ck('launch-and-collection-success',launch['ssh_exit_status']==0 and collection['exit_status']==0,{'launch':launch,'collection':collection})
ck('launch-revision',launch['launch_revision']==plan['launch_revision']==result['capture_revision'],{'launch':launch['launch_revision'],'plan':plan['launch_revision'],'result':result['capture_revision']})
ck('runner-sha',sha(BASE/'remote.py')==argv['remote_script_sha256']==launch['remote_script_sha256']==plan['candidate_remote_script_sha256'],{'sha':sha(BASE/'remote.py')})
ck('launch-runner-source-rev',sha(BASE/'launch.py')==plan['launch_script_sha256'],{'sha':sha(BASE/'launch.py')})
ck('only-monomorphize-and-destination-delta',new==old_norm and not command['monomorphize'],{'removed':'--monomorphize','new_destination':new[new.index('--dest-file')+1]})
ck('fixed-input/tool/source/baseline-pins',command['source_hashes']==result['source_hashes_before_after']['before']==result['source_hashes_before_after']['after'] and command['baseline_sha256']==result['baseline_sha256_before_after'][0]==result['baseline_sha256_before_after'][1],{'source_hashes':len(command['source_hashes']),'baseline':command['baseline_sha256']})
ck('requested-root-and-no-errors',result['requested_root']=='crate::freeze' and result['has_errors'] is False,{'requested_root':result['requested_root'],'has_errors':result['has_errors']})
ck('saved-output-hashes',llbc.is_file() and sha(llbc)==result['llbc_sha256']=='76eefed780e23eb3243413b913e935dc7a9b661bceeb0fc0346668621ab07fb6' and sha(so)==result['charon_stdout_sha256'] and sha(se)==result['charon_stderr_sha256'],{'llbc_sha256':sha(llbc),'size_bytes':llbc.stat().st_size,'stdout_sha256':sha(so),'stderr_sha256':sha(se)})
wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)',gt).group(1).strip(); rss=int(re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',gt).group(1)); swaps=int(re.search(r'Swaps:\s*(\d+)',gt).group(1)); status=int(re.search(r'Exit status:\s*(\d+)',gt).group(1))
ck('gnu-time-result',wall==result['wall_time']=='0:14.74' and rss==result['peak_rss_kib']==630068 and swaps==result['swap_count']==0 and status==result['charon_exit_status']==result['gnu_time_exit_status']==0,{'wall':wall,'rss_kib':rss,'swaps':swaps,'exit':status})
cg=after['effective_cgroup_after']; cgb=before['effective_cgroup_before']
ck('effective-cgroup-caps',all(cg.get(k)==v for k,v in {'memory.high':'5368709120','memory.max':'7516192768','memory.swap.max':'0','pids.max':'128'}.items()) and all(cgb.get(k)==v for k,v in {'memory.high':'5368709120','memory.max':'7516192768','memory.swap.max':'0','pids.max':'128'}.items()),{'before':cgb,'after':cg})
ck('terminal-cgroup-no-oom-or-swap',cg.get('memory.swap.peak')=='0' and all(re.search(rf'^{k} 0$',cg.get('memory.events',''),re.M) for k in ['oom','oom_kill','oom_group_kill','max']),{'memory.peak':cg.get('memory.peak'),'memory.events':cg.get('memory.events'),'swap_peak':cg.get('memory.swap.peak')})
ck('toolchain-pins',result['charon_toolchain']=='nightly-2026-06-01' and 'commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' in result['rustc_version_verbose'] and result['source_commit']=='cb50ff16b9f1066b8a97dc06da704de2da2fa41c' and result['original_driver_sha256']=='4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938',{'charon':result['charon_toolchain'],'rustc_commit':'14210df0e27ccd7d9e6a05b8085cbd438e4bbc65','charon_source_commit':result['source_commit']})
ck('diagnostic-only-no-axioms',result['formal_axioms']=='N/A; diagnostic LLBC only')
report={'status':'PASS','checks':checks,'result_sha256':sha(OUT/'result.json'),'llbc_sha256':sha(llbc),'interpretation_boundary':'Capture custody and literal LLBC/tooling facts only. No execution, Rust source correspondence, dispatch-equivalence, or security claim.'}
(HERE/'portable-audit-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'checks':len(checks),'llbc_sha256':report['llbc_sha256']},indent=2))
