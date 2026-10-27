from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
receipts=[];good={};seen=set();summary=[]
for n in range(1,101):
 a=f'FJp_{n:03}';p=E/a/'receipt.json';assert p.is_file(),a
 r=json.loads(p.read_text());assert r['attempt']==a
 assert len(r['sources'])==1 and r['sources'][0].startswith('FJp_')
 assert '-M7000' in r['command'] and '-j1' in r['command']
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0 and r['source_revision'] and float(r['wall_seconds'])>=0
 for name,h in r['source_hashes'].items():assert sha(E/a/'sources'/name)==h,(a,name)
 key=(json.dumps(r['source_hashes'],sort_keys=True),json.dumps(r['deps_fingerprint'],sort_keys=True))
 assert key not in seen,('unchanged compile',a);seen.add(key)
 stdout=(E/a/'stdout.log').read_text()
 if r['exit_status']==0:
  assert not re.search(r':\d+:\d+: error',stdout),a
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    m=re.search(r'\[(.*?)\]',line,re.S);assert m,(a,line)
    assert set(x.strip() for x in m[1].split(',') if x.strip())<=allowed,(a,line)
  for name,h in r['source_hashes'].items():good[(name,h)]=a
 receipts.append(r)
 summary.append({k:r[k] for k in ['attempt','sources','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
files=sorted((R/'lean').glob('FJp_*.lean'));sources=[]
for p in files:
 h=sha(p);assert (p.name,h) in good,('missing exact-source pass',p.name)
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe)\s|set_option\s+(maxHeartbeats|maxRecDepth|allowUnsafeReducibility)',s,re.M),p
 sources.append(dict(path=str(p.relative_to(R)),sha256=h,bytes=p.stat().st_size,passing_attempt=good[(p.name,h)]))
targets=json.loads((E/'FJp_audit-targets.json').read_text())
final=receipts[-1];assert final['exit_status']==0
reports={re.match(r"'([^']+)'",x)[1]:x for x in final['print_axioms']}
assert set(targets['theorems'])|{'AspisR1.ARX_Root.deployed'}==set(reports)
assert len(reports)==89 and len(targets['theorems'])==88 and len(files)==79
kernel=(E/'FJp_096/stdout.log').read_text();assert kernel.count('KERNEL ')==8
assert 'definitionally identical' in kernel
assert json.loads((E/'FJp_statement-check.json').read_text())['otherwise_byte_identical_after_exact_name_substitution']
recount=json.loads((E/'FJp_recount.json').read_text());assert recount['removed']==['L143','F3Y_G_L143'] and recount['added']==[]
base='d0bdff6733a070aaf18fd91360b0641a49b3366b'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
assert all(p.startswith('evidence/finish-match4-20261027/') or p.startswith('lean/FJp_') for p in changed),changed
assert not any(p.suffix in {'.olean','.ilean','.so','.elf','.tar','.gz'} for p in E.rglob('*') if p.is_file())
(E/'FJp_sources.json').write_text(json.dumps(sources,indent=2)+'\n')
(E/'FJp_attempts.json').write_text(json.dumps(summary,indent=2)+'\n')
objects=final['deps_fingerprint']['selected_objects']
(E/'FJp_delivered-objects.json').write_text(json.dumps(dict(workspace='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025',scope='Direct import objects of final audit; retained coherent canonical cache, not scratch or a fresh full release replay',objects=objects),indent=2)+'\n')
out=dict(status='pass',lean_attempts=100,compiler_starts=100,passed=sum(r['exit_status']==0 for r in receipts),failed=sum(r['exit_status']!=0 for r in receipts),kani_runs=0,kani_limit=20,current_modules=len(files),exact_source_hash_passes=len(sources),new_theorems=88,final_axiom_reports=89,all_successful_axioms_standard_only=True,limits_all_verified=True,swaps_all_zero=True,unchanged_compile_reruns=0,kernel_statement_comparison='096 passes: exact root, exact/definitional wrapper bodies, exactly two atomic removals',root_source_unchanged_otherwise=True,removed=recount['removed'],delta=recount['delta'],nonvacuity='Old-owner inhabitants and complete old ARX conclusion preserved; conditional real-byte and local strict fixtures reused. No new joint root-premise inhabitant claimed.',scope='Prefix only; no shipped/cfg(kani)/Rust/SBF/package replay/wallet/key operations/push/merge',root_receipt='FJp_087/receipt.json',audit_receipt='FJp_100/receipt.json',max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),total_compile_wall_seconds=sum(float(r['wall_seconds']) for r in receipts),failed_attempts=[r['attempt'] for r in receipts if r['exit_status']!=0])
(E/'FJp_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
