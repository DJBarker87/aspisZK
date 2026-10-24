"""Read-only receipt and source assessment, no Lean replay."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/port16cut-20261024'; L=R/'docs/research/100bit-spend-path-20261013/lean'
def digest(p):
 b=p.read_bytes(); return dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def standard(x):
 for a in x['print_axioms']:
  names=re.findall(r'\[([^]]*)\]',a)
  if names:
   assert {re.sub(r'\.\{[^}]*\}','',n) for n in names[0].split(', ')} <= {'propext','Classical.choice','Quot.sound'},a
accepted={}
for module,attempt in [('Port16CUT_TX2',1),('Port16CUT_Cuts',5),('Port16CUT_Bind',6),('Port16CUT_Driver',7),('Port16CUT_Accounting',9),('Port16CUT_Audit',10)]:
 p=L/(module+'.lean'); rc=E/f'lean-{attempt:03d}/receipt.json';x=json.loads(rc.read_text())
 assert x['exit_status']==0 and x['source_hashes'][p.name]==digest(p)['sha256']
 assert x['swaps']=='0' and x['print_axioms']; standard(x)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by|maxHeartbeats|maxRecDepth)\b',p.read_text())
 accepted[module]={'source':digest(p),'receipt':digest(rc),'result':x}
receipts=[]
for rc in sorted(E.glob('lean-*/receipt.json')):
 x=json.loads(rc.read_text()); assert x['swaps']=='0'
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert all(hashlib.sha256((E/x['attempt']/'sources'/f).read_bytes()).hexdigest()==h for f,h in x['source_hashes'].items())
 receipts.append({'receipt':digest(rc),'attempt':x['attempt'],'exit_status':x['exit_status'],'wall_seconds':x['wall_seconds'],'peak_rss_kib':x['peak_rss_kib'],'swaps':x['swaps']})
assert len(receipts)==10
pins=json.loads((E/'reused-port15-host-pins.json').read_text()); old=json.loads((R/'evidence/port15driver-20261024/source-audit.json').read_text())
reused=[]
for module in ['Port15DRIVER_Cost','Port15DRIVER_Local','Port15DRIVER_TX1']:
 item=old['accepted'][module]
 assert digest(R/item['source']['path'])==item['source']
 assert digest(R/item['receipt']['path'])==item['receipt']
 assert pins[module]['.lean']['sha256']==item['source']['sha256']
 reused.append({'module':module,'source':item['source'],'receipt':item['receipt'],'historical_result':item['result'],'host_pins':pins[module]})
# Confirm the imported TX1 object is exactly the separately pinned retained object.
x=json.loads((E/'lean-001/receipt.json').read_text())
assert x['deps_fingerprint']['selected_objects']['Port15DRIVER_TX1.olean']==pins['Port15DRIVER_TX1']['.olean']
for item in old['reused']:
 assert digest(R/item['source']['path'])==item['source']
 assert digest(R/item['receipt']['path'])==item['receipt']
 reused.append(item)
# Snapshot local reachable source hashes; this is source assessment, not closure replay.
seen={}
def visit(module):
 p=L/(module.replace('.','/')+'.lean')
 if module in seen or not p.is_file(): return
 seen[module]=digest(p)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split(): visit(dep)
for m in accepted: visit(m)
reservations=[]
for p in sorted(E.glob('lean-*-reservation.json')):
 x=json.loads(p.read_text()); assert x['admitted'] and x['reserved_bytes']+x['additional_bytes']<x['limit_bytes']
 reservations.append({'file':digest(p),'reserved_bytes':x['reserved_bytes'],'additional_bytes':x['additional_bytes'],'limit_bytes':x['limit_bytes']})
assert len(reservations)==10
# Original Flow/Driver and all accepted inherited modules are unchanged from assigned base.
for m in ['VTop_Flow','Port1_Driver','Port15DRIVER_Cost','Port15DRIVER_Local','Port15DRIVER_TX1']:
 p=L/(m+'.lean'); original=subprocess.check_output(['git','show','98e705b8ff:'+str(p.relative_to(R))],cwd=R)
 assert original==p.read_bytes(),m
result={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'accepted':accepted,'source_assessment':seen,'reused':reused,'attempts':receipts,'admissions':reservations,
 'budget':{'inherited_actual':239,'inherited_prelean':1,'new_actual':10,'new_prelean_only':0,'actual_total':249,'charged':250,'ceiling':252,'remaining':2,'kani_used':0,'kani_ceiling':20},
 'established':'All-outcome actual Port1_Driver stages/rust <=1046+delegatedWeight; <=1161 conditional on explicit per-op LocalBudgets and weighted<=115. Accounting first reads Q+1161, whole two-pass log Q+2322.',
 'remaining_producer':'Concrete installed rest source budgets and weights satisfying weighted<=115 (root A handoff).',
 'cache_assessment':'Focused pinned imported objects reused; reachable sources assessed, no coherent release replay or new ELF identity gate. Historical full aggregate admission remains unverified.',
 'failed_attempts':{'lean-002':'Cut arithmetic with source evaluation context: default whnf heartbeat exhaustion','lean-003':'Explicit equality transport, same arithmetic-context exhaustion','lean-004':'Local numeric subproof still retained source hypothesis; omega whnf exhaustion; replaced with separate numeric declarations','lean-008':'Missing FS firstReads namespace; generated sorryAx not accepted, replaced by explicit namespace import'}}
(E/'source-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'accepted':list(accepted),'attempts':len(receipts),'charged':250,'remaining':2,'source_hashes':len(seen),'reused':len(reused),'admissions':len(reservations)}))
