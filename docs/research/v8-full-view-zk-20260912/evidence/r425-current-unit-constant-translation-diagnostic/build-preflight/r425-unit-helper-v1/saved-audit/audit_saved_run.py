#!/usr/bin/env python3
"""Read-only consistency audit of the saved R425 helper compiler run."""
import hashlib, json, pathlib, re, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path(__file__).resolve().parent

def read(rel): return (ROOT / rel).read_bytes()
def sha(data): return hashlib.sha256(data).hexdigest()
def j(rel): return json.loads(read(rel))
checks=[]
def check(name, condition, detail): checks.append({"check":name,"pass":bool(condition),"detail":detail})
command=j('command.json'); result=j('result.json'); inputs=json.loads((ROOT.parent/'helper-inputs.json').read_text())
# Source snapshots and reviewed staged inputs.
source_hashes={}
for rel, expected in command['source_sha256'].items():
    actual=sha(read('source/'+rel))
    staged=sha((ROOT.parent/'../../candidate'/pathlib.Path(rel).name).read_bytes()) if False else None
    source_hashes[rel]=actual
    check('saved source snapshot '+rel, actual==expected, {'expected':expected,'actual':actual})
reviewed={
 'src/llbc/UnitConstant.ml': ROOT.parent.parent/'candidate/UnitConstant.reviewed.ml',
 'src/dune': ROOT.parent.parent/'candidate/dune.helper-reviewed',
}
for rel,p in reviewed.items():
    actual=sha(p.read_bytes())
    check('reviewed input equals run snapshot '+rel, actual==source_hashes[rel], {'reviewed_path':str(p),'snapshot_sha256':source_hashes[rel],'reviewed_sha256':actual})
check('source revision consistent', command['source_revision']==result['source_revision']==inputs['source_revision'], command['source_revision'])
check('source hashes consistent across receipts', command['source_sha256']==result['source_sha256']==inputs['source_sha256'], command['source_sha256'])
# Raw GNU time is the compiler's authoritative elapsed/RSS/swap/exit receipt.
time=read('gnu-time.txt').decode()
wall_text=re.search(r'Elapsed \(wall clock\) time .*: ([0-9:]+\.[0-9]+)',time).group(1)
wall_parts=wall_text.split(':')
wall=sum(float(part)*(60**(len(wall_parts)-i-1)) for i,part in enumerate(wall_parts))
rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',time).group(1))
swaps=int(re.search(r'Swaps: (\d+)',time).group(1))
exit_status=int(re.search(r'Exit status: (\d+)',time).group(1))
check('compiler status', exit_status==0 and result['exit_status']==0, {'gnu_time_exit':exit_status,'result_exit':result['exit_status']})
check('container status', (lambda x:x['State']['ExitCode']==0 and x['State']['OOMKilled'] is False)(j('docker-inspect.json')[0]), 'Docker reports exit 0 and OOMKilled=false')
inspect=j('docker-inspect.json')[0]
hc=inspect['HostConfig']
check('resource/network scope', hc['MemoryReservation']==5368709120 and hc['Memory']==7516192768 and hc['MemorySwap']==7516192768 and hc['PidsLimit']==128 and hc['NetworkMode']=='none' and hc['CgroupParent']=='aspisr425.slice', {'reservation_bytes':hc['MemoryReservation'],'memory_bytes':hc['Memory'],'memory_swap_bytes':hc['MemorySwap'],'pids':hc['PidsLimit'],'network':hc['NetworkMode'],'cgroup_parent':hc['CgroupParent']})
check('GNU time measurements', wall==7.49 and rss==479152 and swaps==0, {'wall_seconds':wall,'peak_rss_kib':rss,'swaps':swaps})
reservation=j('reservation-before.json')
check('host systemd reservation recorded', 'MemoryHigh=5368709120' in reservation['slice'] and 'MemoryMax=7516192768' in reservation['slice'] and 'MemorySwapMax=0' in reservation['slice'] and 'TasksMax=128' in reservation['slice'], reservation['slice'])
current_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT.parents[3],text=True).strip()
check('compile revision is preserved separately from current checkout', command['source_revision']=='a3fe5df6b53caa52322339906642de5064fc2bbb', {'compile_revision':command['source_revision'],'current_checkout_revision':current_revision})
check('target and mode', command['target']=='.aeneas.objs/byte/aeneas__UnitConstant.cmo' and '--profile release' in command['inner_command'] and '-j 1' in command['inner_command'], {'target':command['target'],'inner_command':command['inner_command']})
check('axiom report correctly N/A', command['axioms']=='NA: OCaml compilation only', command['axioms'])
check('build log saved', len(read('build.log'))==0, 'build.log is empty; success status is independently recorded by GNU time and Docker inspect')
checksums={p.name:sha(p.read_bytes()) for p in [ROOT/'command.json',ROOT/'result.json',ROOT/'gnu-time.txt',ROOT/'build.log',ROOT/'docker-inspect.json',ROOT/'reservation-before.json',ROOT.parent/'helper-inputs.json',ROOT.parent.parent/'candidate/UnitConstant.reviewed.ml',ROOT.parent.parent/'candidate/dune.helper-reviewed']}
metrics={
 'target':command['target'],'source_revision':command['source_revision'],'current_checkout_revision_at_audit':current_revision,'source_sha256':source_hashes,
 'exit_status':exit_status,'wall_seconds':wall,'peak_rss_kib':rss,'swaps':swaps,
 'resource_scope':{'container_memory_reservation_bytes':hc['MemoryReservation'],'container_memory_max_bytes':hc['Memory'],'container_memory_swap_bytes':hc['MemorySwap'],'pids_limit':hc['PidsLimit'],'network':hc['NetworkMode'],'cgroup_parent':hc['CgroupParent']},
 'axioms':'Not applicable: this is an OCaml compiler target, not a Lean theorem.',
 'compiler_receipt_sha256':sha(read('gnu-time.txt')),'input_artifact_sha256':checksums
}
(OUT/'metrics-receipt.json').write_text(json.dumps(metrics,indent=2)+'\n')
audit={'result':'PASS' if all(x['pass'] for x in checks) else 'FAIL','scope':'Saved R425 UnitConstant helper compilation evidence only; no build/test/translation rerun.','checks':checks,'raw_artifact_sha256':checksums}
(OUT/'audit.json').write_text(json.dumps(audit,indent=2)+'\n')
(OUT/'REPORT.md').write_text('# R425 saved helper-run audit\n\n'+audit['result']+' — '+audit['scope']+'\n\nThe isolated release-profile Dune target completed with exit status 0; GNU time records 7.49 s wall, 479152 KiB peak RSS, and zero swaps. Docker inspect records the 5 GiB reservation, 7 GiB memory limit, equal memory-swap setting (no extra container swap), 128 PID limit, no network, and `aspisr425.slice` parent. The run source snapshots match the reviewed helper and Dune input hashes. `#print axioms` is not applicable to this OCaml compile. This records helper compilation only, not fixture execution, Aeneas translation, or Lean proof.\n')
print(audit['result'])
for c in checks:
 print(('PASS' if c['pass'] else 'FAIL')+' '+c['check'])
