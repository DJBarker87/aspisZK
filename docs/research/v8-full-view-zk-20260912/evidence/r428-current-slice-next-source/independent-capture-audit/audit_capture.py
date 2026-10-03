#!/usr/bin/env python3
"""Read-only consistency check for the saved R428 Charon capture."""
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
OUT = BASE / 'saved-output'
def load(path: Path): return json.loads(path.read_text())
def sha(path: Path): return hashlib.sha256(path.read_bytes()).hexdigest()
def check(ok: bool, label: str, details=None):
    checks.append({'check':label,'ok':bool(ok),'details':details})
    if not ok: raise AssertionError(f'{label}: {details!r}')

checks=[]
res=load(OUT/'result.json')
plan=load(BASE/'planned-command.json')
cmd=load(OUT/'extract-command.json')
runner=load(OUT/'runner-status.json')
before=load(OUT/'host-reservation-before.json')
after=load(OUT/'host-reservation-after.json')
llbc_path=OUT/'R428SliceNextSource.llbc'
stdout=OUT/'charon.stdout.log'; stderr=OUT/'charon.stderr.log'; gnu=OUT/'gnu-time.txt'

# Artifact hashes and exact byte counts.
for label,path,key,bytes_key in [
 ('LLBC',llbc_path,'llbc_sha256',None),
 ('stdout',stdout,'charon_stdout_sha256','charon_stdout_bytes'),
 ('stderr',stderr,'charon_stderr_sha256','charon_stderr_bytes')]:
    actual=sha(path)
    check(actual==res[key],f'{label} sha256',{'actual':actual,'receipt':res[key]})
    if bytes_key:
        check(path.stat().st_size==res[bytes_key],f'{label} byte count',{'actual':path.stat().st_size,'receipt':res[bytes_key]})

# GNU time and runner receipts agree exactly with saved result metrics.
time=gnu.read_text()
wall_match=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)',time)
rss_match=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',time)
swap_match=re.search(r'Swaps:\s*(\d+)',time)
exit_match=re.search(r'Exit status:\s*(\d+)',time)
check(bool(wall_match and rss_match and swap_match and exit_match),'GNU time fields present')
check(wall_match.group(1)==res['wall_time'],'wall time agrees',{'gnu_time':wall_match.group(1),'result':res['wall_time']})
check(int(rss_match.group(1))==res['peak_rss_kib'],'peak RSS agrees',{'gnu_time_kib':int(rss_match.group(1)),'result_kib':res['peak_rss_kib']})
check(int(swap_match.group(1))==res['swap_count']==0,'swap agrees and is zero',{'gnu_time':int(swap_match.group(1)),'result':res['swap_count']})
check(int(exit_match.group(1))==res['gnu_time_exit_status']==res['charon_exit_status']==0,'exit statuses agree and are zero')
check(runner['status']=='terminal' and runner['code']==0,'runner terminal status',runner)

# The immutable selected input pins stayed byte-identical before/after.
expected_sources=before['source_hashes_before']
check(expected_sources==after['source_hashes_after'],'source/Cargo hash pins stable',expected_sources)
expected_std=before['stdlib_hashes_before']
check(expected_std==after['stdlib_hashes_after'],'stdlib source hash pins stable',expected_std)
base_sha='9ed7c0ab91051ac61d812d66651680112ac26fe907faa76f9d4d2d9a14d03442'
check(before['baseline_sha_before']==after['baseline_sha_after']==base_sha,'baseline LLBC pin stable',base_sha)
check(res['baseline_sha256_before_after']==[base_sha,base_sha],'result baseline pins match')
check(res['source_hashes_before_after']['before']==res['source_hashes_before_after']['after']==expected_sources,'result source pins match')
check(res['source_revision_recorded']=='d4bf07b08443136de0a11fc1fd932bd604586c2e','extraction source revision recorded',res['source_revision_recorded'])
check(res['capture_revision']==load(BASE/'launch-status.json')['launch_revision'],'capture launch revision agrees')
check(res['rustc_version_verbose'].find('commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65')>=0,'pinned rustc version receipt')

# Requested command is exactly the baseline command plus one include and a new output path.
base_cmd=load(BASE.parent/'base-r327'/'extract-command.json')['command']
new_cmd=cmd['command']; planned=plan['command']
check(new_cmd==planned,'planned and executed commands are identical')
added=['--include','core::slice::iter::_::next']
stripped=[]; i=0
while i<len(new_cmd):
    if new_cmd[i:i+2]==added:
        i+=2; continue
    stripped.append(new_cmd[i]); i+=1
# Only --dest-file's path differs after removing the sole scope addition.
def normalize_dest(xs):
    ys=list(xs)
    j=ys.index('--dest-file'); ys[j+1]='<DESTINATION>'
    return ys
check(normalize_dest(stripped)==normalize_dest(base_cmd),'command differs from R327 base only by selected next include and output destination',{'added_include':added,'base_dest':base_cmd[base_cmd.index('--dest-file')+1],'new_dest':new_cmd[new_cmd.index('--dest-file')+1]})
check(plan['only_scope_delta']==added and plan['monomorphize'] is True,'launch plan declares only one include delta')
check(res['requested_root']=='crate::circle_norm::joined_inverse::line_norm::r110_norm::batch','requested root recorded')
check(res['has_errors'] is False and res['llbc_exists'] is True,'LLBC present and has_errors false')

# Effective process cgroup, events, command caps and host reservation.
for label,cg in [('before',before['effective_cgroup_before']),('result',runner['effective_cgroup']),('after',after['effective_cgroup_after'])]:
    values=(cg['memory.high'],cg['memory.max'],cg['memory.swap.max'],cg['pids.max'])
    check(values==('5368709120','7516192768','0','128'),f'{label} effective cgroup caps',values)
check(runner['effective_cgroup']['memory.events']=='low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0','effective cgroup memory events clean',runner['effective_cgroup']['memory.events'])
check(runner['effective_cgroup']['memory.swap.current']=='0' and runner['effective_cgroup']['memory.swap.peak']=='0','effective cgroup swap usage zero')
check(int(runner['effective_cgroup']['memory.peak'])<7516192768,'cgroup peak below configured maximum',runner['effective_cgroup']['memory.peak'])
check(before['caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'planned explicit caps',before['caps'])
check(before['existing_aspis_slices']==[] and before['other_active_aspis_services']==[] and before['heavy_processes']==[],'saved host reservation had no conflicting Aspis workload')

# Parse LLBC shape without executing or compiling it.
llbc=load(llbc_path); translated=llbc['translated']
check(llbc['has_errors'] is False,'native LLBC has_errors false')
fun0=next(f for f in translated['fun_decls'] if f['def_id']==0)
fun10=next(f for f in translated['fun_decls'] if f['def_id']==10)
def id_names(fun): return [part['Ident'][0] for part in fun['item_meta']['name'] if 'Ident' in part]
check(id_names(fun0)[-1]=='batch' and fun0['body'] is not None and fun0['item_meta']['opacity']=='Transparent','root Fun0 emitted with transparent body',{'id':0,'name':id_names(fun0),'opacity':fun0['item_meta']['opacity'],'body':fun0['body'] is not None})
check(id_names(fun10)[-1]=='next' and fun10['body'] is not None and fun10['item_meta']['opacity']=='Transparent','function 10 SliceIter.next emitted with transparent body',{'id':10,'name':id_names(fun10),'opacity':fun10['item_meta']['opacity'],'body':fun10['body'] is not None})
span=fun10['body']['Structured']['span']['data']
check(span['beg']['line']==157 and span['end']['line']==192,'Fun10 source span matches saved macro next body',span)
check(res['formal_axioms']=='N/A; diagnostic LLBC only','axiom status correctly N/A for extraction')

report={
 'status':'PASS' if all(x['ok'] for x in checks) else 'FAIL',
 'classification':'read-only saved-capture consistency audit; no build, re-extraction, proof, or source-semantics claim',
 'checks':checks,
 'artifacts':{str(p.relative_to(BASE)):sha(p) for p in [llbc_path,stdout,stderr,gnu,OUT/'result.json',OUT/'extract-command.json',OUT/'runner-status.json',OUT/'host-reservation-before.json',OUT/'host-reservation-after.json',BASE/'planned-command.json']},
 'summary':{'charon_exit':res['charon_exit_status'],'wall_time':res['wall_time'],'peak_rss_kib':res['peak_rss_kib'],'swap_count':res['swap_count'],'llbc_has_errors':llbc['has_errors'],'root_fun_id':0,'slice_next_fun_id':10,'formal_axioms':'N/A'},
 'scope_note':'The audit verifies saved command/receipt/hash/resource/LLBC facts only. It does not prove runtime behavior, MIR ownership semantics, pointer safety, actual QM31 layout, or Rust-to-Lean correspondence.'
}
(BASE/'independent-capture-audit'/'audit-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'checks':len(checks),'failed':[c for c in checks if not c['ok']],'report':str(BASE/'independent-capture-audit'/'audit-report.json')},indent=2))
