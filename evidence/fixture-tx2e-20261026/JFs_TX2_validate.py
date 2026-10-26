from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]
for n in range(1,101):
 p=P/f'JFs_TX2_{n:03}'/'receipt.json';d=json.loads(p.read_text())
 assert d['attempt']==f'JFs_TX2_{n:03}'
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in d['command'] and d['swaps']=='0'
 for mod,h in d['source_hashes'].items():assert sha(p.parent/'sources'/mod)==h
 if d['exit_status']==0:
  for a in d['print_axioms']:
   assert not any(x in a for x in ['sorryAx','native_decide','Lean.ofReduceBool']),a
   if 'depends on axioms:' in a:
    assert set(re.search(r'\[(.*)\]',a)[1].split(', ')) <= {'propext','Classical.choice','Quot.sound'},a
 receipts.append(d)
accepted=[]
for src in sorted((R/'lean').glob('JFs_TX2_*.lean')):
 matches=[d for d in receipts if d['exit_status']==0 and d['source_hashes'].get(src.name)==sha(src)]
 assert matches,src
 d=matches[-1]
 for th in re.findall(r'^theorem\s+(\w+)',src.read_text(),re.M):
  assert '#print axioms '+th in src.read_text(),(src,th)
  assert any('.'+th+"' " in a for a in d['print_axioms']),(src,th,d['attempt'])
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)',src.read_text(),re.M),src
 accepted.append({'module':src.stem,'sha256':sha(src),'accepted_attempt':d['attempt'],'print_axioms':d['print_axioms']})
base='3a6011ef8a6b6ff5f1ba0fd34edd6cfc09315239'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(x.startswith('lean/JFs_TX2_') or x.startswith('evidence/fixture-tx2e-20261026/') for x in changed+untracked),changed
assert not any(x.endswith(('.olean','.elf','.so','.tar','.gz')) for x in changed+untracked)
assert (P/'JFs_TX2_BEFORE_Rc10_Top.lean.txt').read_bytes()==(R/'lean/Rc10_Top.lean').read_bytes()==(P/'JFs_TX2_AFTER_Rc10_Top.lean.txt').read_bytes()
summary={'lean_attempts':100,'passing':sum(d['exit_status']==0 for d in receipts),'rejected':sum(d['exit_status']!=0 for d in receipts),'kani_runs':0,'kani_budget':10,'accepted_modules':len(accepted),'total_lean_wall_seconds':sum(d['wall_seconds'] for d in receipts),'maximum_peak_rss_kib':max(int(d['peak_rss_kib']) for d in receipts),'total_swaps':sum(int(d['swaps']) for d in receipts),'reservation_retries':sum(len(json.loads((P/f"{d['attempt']}-retries.json").read_text())) for d in receipts),'final_audit':receipts[-1],'actual_top_delta':{'T':0,'P':0,'G':0,'C':0},'accepted2':False,'full_real_sha256_native_pair_nonvacuity':False}
for name,data in [('JFs_TX2_RECORDS_MANIFEST.json',receipts),('JFs_TX2_VALIDATION.json',accepted),('JFs_TX2_SUMMARY.json',summary)]:
 (P/name).write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='final_audit'},indent=2))
