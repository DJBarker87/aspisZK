"""Read-only source/receipt assessment; no Lean or build launch."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; E=R/'evidence/port15driver-20261024'; L=R/'docs/research/100bit-spend-path-20261013/lean'
def digest(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
accepted={}
for module,attempt in [('Port15DRIVER_Cost',1),('Port15DRIVER_Local',2),('Port15DRIVER_TX1',19)]:
 p=L/(module+'.lean');rc=E/f'lean-{attempt:03d}/receipt.json';x=json.loads(rc.read_text())
 assert x['exit_status']==0 and x['source_hashes'][p.name]==digest(p)['sha256']
 assert x['swaps']=='0' and x['print_axioms']
 assert all('sorryAx' not in a and set(re.findall(r'\[([^]]*)\]',a)[0].split(', '))<= {'propext','Classical.choice','Quot.sound'} for a in x['print_axioms'])
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|maxHeartbeats|maxRecDepth)\b',p.read_text())
 accepted[module]={'source':digest(p),'receipt':digest(rc),'result':x}
receipts=[]
for rc in sorted(E.glob('lean-*/receipt.json')):
 x=json.loads(rc.read_text());receipts.append({'receipt':digest(rc),'attempt':x['attempt'],'exit_status':x['exit_status'],'wall_seconds':x['wall_seconds'],'peak_rss_kib':x['peak_rss_kib'],'swaps':x['swaps']})
assert len(receipts)==21
# Pin every locally available import source reachable from the accepted roots,
# plus the unproved driver target. This assesses sources, not coherent cache identity.
seen={}
def visit(module):
 p=L/(module.replace('.','/')+'.lean')
 if module in seen or not p.is_file():return
 seen[module]=digest(p)
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():visit(dep)
for m in [*accepted,'Port1_Driver']:visit(m)
old=json.loads((R/'evidence/port14local-20261024/source-audit.json').read_text());reused=[]
for item in old['reused']:
 if item['module'] not in ['Port12COUNT_Installed','Port12COUNT_Batch','Port11PROV_SourceCount','Port9OR_Budget']:continue
 assert digest(R/item['source']['path'])==item['source']
 assert digest(R/item['receipt']['path'])==item['receipt']
 reused.append(item)
# Add exact historical writer/reader cap receipts, matching current source bytes.
for module,folder in [('Port11PROV_SourceCount','port11prov-20261024'),('Port9OR_Budget','port9oracle-20261024')]:
 source=L/(module+'.lean');matches=[]
 for rc in (R/'evidence'/folder).glob('lean-*/receipt.json'):
  x=json.loads(rc.read_text())
  if x['exit_status']==0 and x.get('source_hashes',{}).get(source.name)==digest(source)['sha256']:
   matches.append((rc,x))
 assert matches,module
 rc,x=sorted(matches,key=lambda pair:str(pair[0]))[-1]
 reused.append({'module':module,'source':digest(source),'receipt':digest(rc),'historical_result':x})
reservations=[]
for p in sorted(E.glob('lean-*-reservation.json')):
 x=json.loads(p.read_text());assert x['admitted'] and x['reserved_bytes']+x['additional_bytes']<x['limit_bytes']
 reservations.append(digest(p))
assert len(reservations)==21
result={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'accepted':accepted,'source_assessment':seen,'reused':reused,'attempts':receipts,'admissions':reservations,
 'budget':{'inherited_actual':218,'inherited_prelean':1,'new_actual':21,'new_prelean_only':0,'charged':240,'ceiling':240,'remaining':0,'kani_used':0,'kani_ceiling':20},
 'established':'Actual TX1 all-outcome Fits bound under explicit LocalBudgets; no success assumption',
 'unproved':'Full stages/rust composition: default-heartbeat timeout in lean-020/021; no accepted driver module',
 'partial':'TX2 declaration standard-axiom report in failed lean-020/021; NOT a green module receipt',
 'cache_assessment':'Focused pinned imported objects reused. Source hashes assessed; not a coherent closure replay or new release identity gate.'}
(E/'source-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'accepted':list(accepted),'new_attempts':len(receipts),'remaining':0,'source_hashes':len(seen),'reused_receipts':len(reused),'admissions':len(reservations)}))
