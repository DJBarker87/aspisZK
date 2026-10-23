#!/usr/bin/env python3
"""Read-only verification of this packet's final source and focused receipts."""
from pathlib import Path
import hashlib,json,re,subprocess
base=Path(__file__).resolve().parent
project=base.parents[1]
allowed={'propext','Classical.choice','Quot.sound'}
green={'S2B_FirstReturn':3,'S2B_OriginalInputs':5,'S2B_Syscalls':8,
       'S2B_ChildEffects':10,'S2B_LeadCarriers':15,'S2B_SameReturnEffects':16}
all_attempts=sorted(base.glob('lean-*/receipt.json'))
assert len(all_attempts)<=100
rows=[]
for module,n in green.items():
 receipt=json.loads((base/f'lean-{n:03}/receipt.json').read_text())
 source=project/'lean'/f'{module}.lean'
 assert receipt['exit_status']==0,(module,receipt['exit_status'])
 assert hashlib.sha256(source.read_bytes()).hexdigest()==receipt['source_hashes'][source.name]
 assert receipt['swaps']=='0'
 assert receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 text=source.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxRecDepth|maxHeartbeats)\b',text)
 names=re.findall(r'^theorem\s+(\w+)',text,re.M)
 assert len(names)==len(receipt['print_axioms']),(module,names)
 for name,line in zip(names,receipt['print_axioms']):
  assert f'.{name}\'' in line,(name,line)
  ax=re.search(r'\[(.*?)\]',line)
  assert ax is not None and set(ax.group(1).split(', '))<=allowed,line
 rows.append({'module':module,'attempt':n,'source_sha256':receipt['source_hashes'][source.name],
              'receipt':f'lean-{n:03}/receipt.json','source_revision':receipt['source_revision'],
              'exit':0,'wall_seconds':receipt['wall_seconds'],'peak_rss_kib':int(receipt['peak_rss_kib']),
              'swap':0,'print_axioms':receipt['print_axioms']})
pins=json.loads((base/'source-pins.json').read_text())
assert pins['shipped_diff']==''
result={'schema':'focused-extractor-proof-packet-v1','status':'conditional local integration only; S2 open',
 'native_execution_certificate_constructed':False,'native_oracle_trace_refinement_proved':False,
 'new_sdk_trust_added':False,'source_revision_note':'Each receipt records checkout parent plus exact changed-source SHA and source snapshot. Imported caches were reused, not a coherent release rebuild.',
 'lean_compile_attempts_used':len(all_attempts),'lean_compile_attempt_limit':100,'kani_runs_used':0,'kani_run_limit':60,
 'green':rows,'failed_attempts':[{'attempt':p.parent.name,'exit':json.loads(p.read_text())['exit_status'],'receipt':str(p.relative_to(base))} for p in all_attempts if json.loads(p.read_text())['exit_status']!=0],
 'aggregate_replay':'No package/frozen-release manifest replay; enclosing native result absent.',
 'shipped_source_changed':False,'elf_rebuilt':False,'full_native_claim':'target not yet established'}
(base/'manifest.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'audit':'PASS','lean_compile_attempts_used':len(all_attempts),'kani_runs_used':0,'final_modules':list(green),'native_claim':'S2 OPEN'}))
