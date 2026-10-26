"""Validate retained Rc7 receipts and source scope without running provers."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
receipts=[];modules={};axioms=[]
for i in range(1,61):
 p=E/f'Rc7_{i:03}';r=load(p/'receipt.json');assert r['exit_status']==0,(i,r['exit_status'])
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and '-j1' in r['command']
 assert int(r['swaps'])==0
 for s,h in r['source_hashes'].items():
  assert sha(p/'sources'/s)==h,(i,s)
  assert sha(R/'lean'/s)==h,(i,s,'changed after compile')
  modules[s]=i
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   names=set(line.rsplit('[',1)[1].split(']')[0].replace(',',' ').split())
   assert names<={'propext','Classical.choice','Quot.sound'},(i,line)
   axioms.append(line)
  else:assert 'does not depend on any axioms' in line,(i,line)
 assert load(E/(p.name+'-reservation.json'))['allowed']
 receipts.append(r)
assert len(modules)==60,len(modules)
proof=['Rc7_Native.accepted','Rc7_Top.deployed','Rc7_Install.headline','Rc7_Install.native','Rc7_Reverse.same_witnesses','Rc7_Nonvacuity.composed','Rc7_Event.single','Rc7_Clean.exists_world','Rc7_AcceptedInput.accepted_input']
assert all(any(n in l for l in axioms) for n in proof)
for p in (R/'lean').glob('Rc7_*.lean'):
 assert p.name in modules,p
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|sorryAx)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text()),p
 assert not re.search(r'[ \t]+$',p.read_text(),re.M),p
pins=load(E/'Rc7_source_check.json');assert not pins['substantive_mismatches']
# Every tracked final delta must be in the explicitly allowed scope.
files=set(subprocess.check_output(['git','diff','--name-only','082349cc6e'],cwd=R,text=True).splitlines())
files.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines())
assert all(x.startswith(('lean/Rc7_','evidence/recount7-20261026/')) or x=='design/PREMISE-LEDGER-20261025.md' for x in files),files
assert not any(Path(f).suffix in {'.olean','.o','.elf','.so','.dylib','.tar','.gz','.pyc'} for f in files)
summary=dict(status='passed',lean_attempts=60,lean_successes=60,kani_runs=0,package_replay=False,wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,modules=len(modules),new_theorem_audits=proof,axioms=sorted(set(axioms)),reservation_retries=sum(len(load(E/(r['attempt']+'-retries.json'))) for r in receipts),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),cache=dict(modules=pins['modules'],source_compared=pins['source_compared'],comment_only_variants=pins['comment_only_variants'],substantive_mismatches=[]))
(E/'Rc7_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'Rc7_ATTEMPTS.jsonl').write_text(''.join(json.dumps({k:r[k] for k in ['attempt','sources','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})+'\n' for r in receipts))
print(json.dumps({k:v for k,v in summary.items() if k!='axioms'},indent=2))
