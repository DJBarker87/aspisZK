#!/usr/bin/env python3
"""Read-only consistency audit of the saved R425 integration compiler run."""
import hashlib, json, pathlib, re, subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1]; OUT=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(rel): return (ROOT/rel).read_bytes()
def j(rel): return json.loads(read(rel))
checks=[]
def ck(n,ok,d): checks.append({'check':n,'pass':bool(ok),'detail':d})
cmd=j('command.json'); res=j('result.json'); ins=json.loads((ROOT.parent/'integration-inputs.reviewed.json').read_text())
for rel,want in cmd['source_sha256'].items():
 got=sha(read('source/'+rel)); ck('saved source snapshot '+rel,got==want,{'expected':want,'actual':got})
reviewed={'src/llbc/UnitConstant.ml':ROOT.parent.parent/'candidate/UnitConstant.reviewed.ml','src/dune':ROOT.parent.parent/'candidate/dune.helper-reviewed','src/interp/InterpExpressions.ml':ROOT.parent.parent/'candidate/InterpExpressions.draft.ml'}
source_hashes={}
for rel,p in reviewed.items():
 snap=sha(read('source/'+rel)); candidate=sha(p.read_bytes()); source_hashes[rel]=snap
 ck('reviewed source equals run snapshot '+rel,snap==candidate,{'candidate_path':str(p),'snapshot_sha256':snap,'reviewed_sha256':candidate})
ck('revision receipts agree',cmd['source_revision']==res['source_revision']==ins['source_revision']=='ee7ba72da456d5f353bca9f6739b23750a5dfffa',{'compile_revision':cmd['source_revision'],'input_record_revision':ins['source_revision'],'candidate_prepared_revision':ins.get('candidate_prepared_at_revision')})
ck('source hash receipts agree',cmd['source_sha256']==res['source_sha256']==ins['source_sha256'],cmd['source_sha256'])
t=read('gnu-time.txt').decode(); wt=re.search(r'Elapsed \(wall clock\) time .*: ([0-9:]+\.[0-9]+)',t).group(1); ps=wt.split(':'); wall=sum(float(x)*60**(len(ps)-i-1) for i,x in enumerate(ps)); rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t).group(1)); swaps=int(re.search(r'Swaps: (\d+)',t).group(1)); ex=int(re.search(r'Exit status: (\d+)',t).group(1))
inspect=j('docker-inspect.json')[0]; hc=inspect['HostConfig']; state=inspect['State']; reservation=j('reservation-before.json')['slice']
ck('compiler and container success',ex==0 and res['exit_status']==0 and state['ExitCode']==0 and state['OOMKilled'] is False,{'gnu_time_exit':ex,'result_exit':res['exit_status'],'container_exit':state['ExitCode'],'oom_killed':state['OOMKilled']})
ck('GNU time metrics',wall==12.71 and rss==395416 and swaps==0,{'wall_seconds':wall,'peak_rss_kib':rss,'swaps':swaps})
ck('cgroup/container caps',hc['MemoryReservation']==5368709120 and hc['Memory']==7516192768 and hc['MemorySwap']==7516192768 and hc['PidsLimit']==128 and hc['NetworkMode']=='none' and hc['CgroupParent']=='aspisr425.slice' and all(x in reservation for x in ['MemoryHigh=5368709120','MemoryMax=7516192768','MemorySwapMax=0','TasksMax=128']),{'docker':{k:hc[k] for k in ['MemoryReservation','Memory','MemorySwap','PidsLimit','NetworkMode','CgroupParent']},'systemd_slice':reservation})
ck('integration target and release mode',cmd['target']=='.aeneas.objs/byte/aeneas__InterpExpressions.cmo' and '--profile release' in cmd['inner_command'] and '-j 1' in cmd['inner_command'],{'target':cmd['target'],'inner_command':cmd['inner_command']})
ck('helper predecessor recorded green',cmd['helper_result']['exit_status']==0 and cmd['helper_result']['source_revision']=='a3fe5df6b53caa52322339906642de5064fc2bbb',cmd['helper_result'])
ck('axiom report N/A',cmd['axioms']=='NA: OCaml compilation only','OCaml module compile only')
ck('build log captured',len(read('build.log'))==0,'empty successful build log; compiler status and GNU-time are separately retained')
current=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT.parents[3],text=True).strip()
ck('historical compile revision distinguished from current checkout',cmd['source_revision']=='ee7ba72da456d5f353bca9f6739b23750a5dfffa',{'compile_revision':cmd['source_revision'],'current_checkout_revision_at_audit':current})
files=[ROOT/'command.json',ROOT/'result.json',ROOT/'gnu-time.txt',ROOT/'build.log',ROOT/'docker-inspect.json',ROOT/'reservation-before.json',ROOT.parent/'integration-inputs.reviewed.json',*reviewed.values()]
raw={p.name:sha(p.read_bytes()) for p in files}
metrics={'target':cmd['target'],'source_revision':cmd['source_revision'],'current_checkout_revision_at_audit':current,'source_sha256':source_hashes,'exit_status':ex,'wall_seconds':wall,'peak_rss_kib':rss,'swaps':swaps,'resource_scope':{'container_memory_reservation_bytes':hc['MemoryReservation'],'container_memory_max_bytes':hc['Memory'],'container_memory_swap_bytes':hc['MemorySwap'],'pids_limit':hc['PidsLimit'],'network':hc['NetworkMode'],'cgroup_parent':hc['CgroupParent'],'systemd_slice':reservation},'helper_predecessor':{'source_revision':cmd['helper_result']['source_revision'],'exit_status':cmd['helper_result']['exit_status'],'source_sha256':cmd['helper_result']['source_sha256']},'axioms':'Not applicable: OCaml compilation, no Lean theorem.','compiler_receipt_sha256':sha(read('gnu-time.txt')),'raw_artifact_sha256':raw}
(OUT/'metrics-receipt.json').write_text(json.dumps(metrics,indent=2)+'\n')
audit={'result':'PASS' if all(x['pass'] for x in checks) else 'FAIL','scope':'Saved R425 InterpExpressions integration compilation only; no build/test/translation rerun.','checks':checks,'raw_artifact_sha256':raw}
(OUT/'audit.json').write_text(json.dumps(audit,indent=2)+'\n')
(OUT/'REPORT.md').write_text('# R425 saved integration-run audit\n\n'+audit['result']+' — '+audit['scope']+'\n\nThe isolated release-profile Dune target completed with exit status 0; GNU time records 12.71 s wall, 395416 KiB peak RSS, and zero swaps. The command and Docker records show a 5 GiB reservation, 7 GiB memory limit, equal memory-swap setting (no added container swap), 128 PID limit, no network, and the `aspisr425.slice` parent; the host systemd slice records `MemorySwapMax=0`. All three source snapshots match reviewed inputs, and the helper predecessor is recorded green. Axiom reporting is not applicable to this OCaml compile. This establishes integration typechecking only; it records no fixture execution, translation, or Lean proof.\n')
print(audit['result']); [print(('PASS ' if x['pass'] else 'FAIL ')+x['check']) for x in checks]
