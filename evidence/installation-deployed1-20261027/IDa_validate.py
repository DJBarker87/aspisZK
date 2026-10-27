"""Validate owned sources, focused receipts, standard axioms and unchanged pins."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent; R=E.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
b=json.loads((E/'IDa_BASELINE.json').read_text()); receipts=[]
for n in range(1,5):
 p=E/f'IDa_{n:03}'/'receipt.json'; x=json.loads(p.read_text())
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in x['command'] and '-j1' in x['command']
 for name,h in x['source_hashes'].items(): assert sha(p.parent/'sources'/name)==h
 for line in x['print_axioms']:
  ax=line.split('depends on axioms: [')[-1].removesuffix(']')
  ax=re.sub(r'\.\{[^}]*\}', '', ax)
  assert set(ax.split(', '))<={'propext','Classical.choice','Quot.sound'},line
 receipts.append(x)
assert [x['exit_status'] for x in receipts]==[1,0,0,0]
assert 'maximum number of heartbeats' in (E/'IDa_001/stdout.log').read_text()
assert receipts[0]['source_hashes']!=receipts[1]['source_hashes']
modules=[]
for p in sorted((R/'lean').glob('IDa_*.lean')):
 s=p.read_text(); h=sha(p)
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(?:maxHeartbeats|maxRecDepth)',s,re.M),p
 passed=[x['attempt'] for x in receipts if x['exit_status']==0 and x['source_hashes'].get(p.name)==h]
 assert passed,p
 modules.append(dict(path=str(p.relative_to(R)),sha256=h,passing_attempts=passed))
expected=['AspisR1.IDa_Deployed.'+n for n in ['selected_fields','terminal_fixed','finish_fixed','boundaries_fixed','ARX_Deployed']]+['AspisR1.IDa_Nonvacuity.conditional']
for t in expected: assert any(line.startswith("'"+t+"'") for line in receipts[-1]['print_axioms']),t
for p,h in b['files'].items(): assert sha(R/p)==h,p
changed=subprocess.check_output(['git','diff','--name-only',b['revision']],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/IDa_') or p.startswith('evidence/installation-deployed1-20261027/') for p in changed+untracked)
(E/'IDa_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x,sort_keys=True)+'\n' for x in receipts))
v=dict(lean_attempts=4,lean_budget=40,dependency_builds=0,kani_runs=0,passes=3,errors=1,failed_auxiliary='IDa_001 full-record definitional-equality heartbeat limit; changed to projection facts in IDa_002',wall_timeouts=0,memory_kills=0,unchanged_reruns=0,cap_increases=0,own_simultaneous_scopes=1,modules=modules,all_new_top_theorems_audited=expected,axioms=['propext','Classical.choice','Quot.sound'],source_baseline_revision=b['revision'],baseline_files_unchanged=True,root_source_unchanged=True,ledger_edited=False,contract_edited=False,shipped_files_changed=False,elf_rebuild_triggered=False,artifact_pins='inherited, not reproduced',scope='focused compilation on reused coherent SInt2 cache; no package/release replay',max_peak_rss_kib=max(int(x['peak_rss_kib']) for x in receipts),swaps=[x['swaps'] for x in receipts],final_audit={k:receipts[-1][k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']},mechanical_type_check=json.loads((E/'IDa_STATEMENT-CHECK.json').read_text()),ledger_delta='0T/0P/0G/0C',nonvacuity='conditional preservation only; no complete joint release inhabitant')
(E/'IDa_VALIDATION.json').write_text(json.dumps(v,indent=2)+'\n')
print(json.dumps({k:v[k] for k in ['lean_attempts','passes','errors','max_peak_rss_kib','all_new_top_theorems_audited','ledger_delta']},indent=2))
