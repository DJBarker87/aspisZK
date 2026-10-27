from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
receipts=[];good={};seen=set();summary=[]
paths=sorted(E.glob('FJu_[0-9][0-9][0-9]/receipt.json'))
for n,p in enumerate(paths,1):
 a=f'FJu_{n:03}';r=json.loads(p.read_text());assert r['attempt']==a
 assert len(r['sources'])==1 and r['sources'][0].startswith('FJu_')
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
assert 0<len(receipts)<=100
files=sorted((R/'lean').glob('FJu_*.lean'));sources=[]
for p in files:
 h=sha(p);assert (p.name,h) in good,('missing exact-source pass',p.name)
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|unsafe)\s|set_option\s+(maxHeartbeats|maxRecDepth|allowUnsafeReducibility)',s,re.M),p
 sources.append(dict(path=str(p.relative_to(R)),sha256=h,bytes=p.stat().st_size,passing_attempt=good[(p.name,h)]))
targets=json.loads((E/'FJu_audit-targets.json').read_text())
final=receipts[-1];assert final['sources']==['FJu_ClosureAudit.lean'] and final['exit_status']==0
reports={re.match(r"'([^']+)'",x)[1]:x for x in final['print_axioms']}
assert set(targets['theorems']+targets['baseline'])==set(reports)
kernel=(E/'FJu_011/stdout.log').read_text();assert kernel.count('KERNEL ')==8
assert 'definitionally identical' in kernel
assert json.loads((E/'FJu_statement-check.json').read_text())['source_type_byte_identical_after_exact_predicate_substitution']
recount=json.loads((E/'FJu_recount.json').read_text());assert recount['removed']==['L144','L145','F3Y_G_L144','F3Y_G_L145'] and recount['added']==[]
base='b54cbda4b1c85d7c3223988a3ad1711c8b734d5d'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
new=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(p.startswith('evidence/finish-chain1-20261027/') or p.startswith('lean/FJu_') for p in changed+new),changed+new
assert not any(p.suffix in {'.olean','.ilean','.so','.elf','.tar','.gz'} for p in E.rglob('*') if p.is_file())
(E/'FJu_sources.json').write_text(json.dumps(sources,indent=2)+'\n')
(E/'FJu_attempts.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'FJu_delivered-objects.json').write_text(json.dumps(dict(workspace='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025',scope='Direct imports of final focused audit; canonical objects retained for lead reuse, not scratch or fresh full release replay',objects=final['deps_fingerprint']['selected_objects']),indent=2)+'\n')
out=dict(status='pass',lean_attempts=len(receipts),compiler_starts=len(receipts),lean_limit=100,passed=sum(r['exit_status']==0 for r in receipts),failed=sum(r['exit_status']!=0 for r in receipts),kani_runs=0,kani_limit=20,current_modules=len(files),exact_source_hash_passes=len(sources),new_theorems=len(targets['theorems']),final_axiom_reports=len(reports),all_successful_axioms_standard_only=True,limits_all_verified=True,swaps_all_zero=True,unchanged_compile_reruns=0,kernel_statement_comparison='011 passes: exact root and exact/definitional wrapper bodies;024 explicitly verifies hypothesis binders',root_source_unchanged_otherwise=True,removed=recount['removed'],delta=recount['delta'],nonvacuity='Owner equivalence and all previous satisfying owner instances preserved; complete original FJp conclusion recovered. Existing conditional real-byte/local strict fixtures reused. No new joint root-premise inhabitant claimed.',scope='Prefix only; no shipped/cfg(kani)/Rust/SBF/package replay/wallet/key/push/merge',root_receipt='FJu_010/receipt.json',audit_receipt=str(paths[-1].relative_to(E)),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),total_compile_wall_seconds=sum(float(r['wall_seconds']) for r in receipts),failed_attempts=[r['attempt'] for r in receipts if r['exit_status']!=0])
(E/'FJu_validation.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
