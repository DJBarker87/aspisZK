from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2f-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(Path(__file__).with_name('S2F_sourcecuts.py')),'--check'],check=True)
assert (E/'S2F-steps/src/S2F_Trusted.rs').read_bytes()==(D/'evidence/s2a-20261023/S2A-spec/S2A_Primitives.rs').read_bytes()
copy_reuse=json.loads((E/'S2F-copy-reuse.json').read_text())
assert sha(E/'S2F-steps/src/S2F_CopyStub.rs')==copy_reuse['callee_and_contract_harness_prefix_sha256']
rows=[];accepted_counts={'lean':0,'kani':0};counts={'lean':0,'kani':0}
for p in sorted(E.glob('*/receipt.json')):
 a=p.parent.name;r=json.loads(p.read_text());kind=r['kind'];counts[kind]+=1
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert r['swaps']=='0' and r['wall_seconds']>=0 and int(r['peak_rss_kib'])>0,a
 assert re.fullmatch('[0-9a-f]{40}',r['source_revision']),a
 for name,want in r['source_hashes'].items():assert sha(p.parent/'sources'/name)==want,(a,name)
 reservation=json.loads((E/(a+'-reservation.json')).read_text());assert reservation['allowed'] and reservation['all_populated_scopes_bounded'],a
 log=(p.parent/'stdout.log').read_text();accepted=r['exit_status']==0
 if accepted:
  accepted_counts[kind]+=1
  if kind=='lean':
   assert r['print_axioms'] and 'sorryAx' not in log,a
   for line in r['print_axioms']:
    m=re.search(r'depends on axioms: \[(.*?)\]',line)
    assert m and set(filter(None,map(str.strip,m.group(1).split(','))))<={'propext','Classical.choice','Quot.sound'},(a,line)
  else:
   assert 'VERIFICATION:- SUCCESSFUL' in log and re.search(r'\*\* 0 of \d+ failed',log),a
   assert '[optimized]' in log,a
 status='accepted focused result' if accepted else 'excluded failure/review stop'
 if kind=='lean' and accepted and a not in ['lean-012','lean-013','lean-017','lean-018','lean-019']:status='superseded focused success; standard audit, earlier statement'
 rows.append(dict(attempt=a,target=r['command'][-1] if kind=='lean' else r['command'][-3],status=status,receipt=str(p.relative_to(D)),exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),swap=0,source_revision=r['source_revision'],print_axioms=r['print_axioms']))
assert counts['lean']<=100 and counts['kani']<=60
for p in (D/'lean').glob('S2F_*.lean'):
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b',p.read_text()),p
final=json.loads((E/'lean-019/receipt.json').read_text());assert final['exit_status']==0 and len(final['print_axioms'])==13
for p in (D/'lean').glob('S2F_*.lean'):assert final['source_hashes'][p.name]==sha(p),p
for name,obj in final['deps_fingerprint']['selected_objects'].items():
 if name.startswith('S2F_'):assert obj['source_sha256']==sha(D/'lean'/(name+'.lean'))
initial=json.loads((E/'S2F-stage0.json').read_text())
for name,pin in initial['sources'].items():assert sha(R/name)==pin['sha256'],name
base=initial['source_revision']
paths=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
allowed=['tools/s2f-20261023/','docs/research/100bit-spend-path-20261013/evidence/s2f-20261023/','docs/research/100bit-spend-path-20261013/lean/S2F_','docs/research/100bit-spend-path-20261013/design/S2F-20261023.md']
assert all(any(p.startswith(root) for root in allowed) for p in paths),paths
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in ['.olean','.elf','.so','.a','.tar','.gz','.out'] and p.stat().st_size<5*2**20,p
out=dict(schema='s2f-focused-source-step-packet-v1',status='PARTIAL: native acceptance to owned E not established',budget_used=counts,accepted_focused_counts=accepted_counts,attempts=rows,final_lean_predecessors=['lean-018','lean-012','lean-013','lean-017'],final_export_audit='lean-019',axioms='standard only in accepted evidence',native_required14_discharged=0,remaining=['full typed native/owned state relation and original full payload port','instantiate concrete per-source-step laws and both E evaluator ports','concrete child native carrier/state/effect/allocator contracts (G inventory remains partial)','native rejection/cleanup/query-prefix and abort/runtime/ELF/P6 ports'],scope='Kani cut projections, verified safe-slice copy dispatch, conditional sequence composition, actual extracted reference stage2 certificate and four local rejection laws; no native enclosing theorem or release claim')
(E/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(budget_used=counts,accepted_focused_counts=accepted_counts,final_print_axioms=len(final['print_axioms']),source_scope='unchanged shipped files',status=out['status'])))
