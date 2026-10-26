"""Validate retained receipts and current source/evidence without a prover rerun."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(P.glob('Rc5_???/receipt.json'))]
assert len(receipts)==60
assert [r['attempt'] for r in receipts]==[f'Rc5_{n:03}' for n in range(1,61)]
failed={r['attempt'] for r in receipts if r['exit_status']!=0}
assert failed=={'Rc5_002','Rc5_004','Rc5_006','Rc5_013','Rc5_023','Rc5_024'}
sources={};theorems={};timeline=[]
for r in receipts:
 d=P/r['attempt'];assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 assert r['command'][1:6]==['env','lean','-j1','-M7000','-DElab.async=false']
 assert r['deps_fingerprint']['selected_objects']
 assert r['deps_fingerprint']['lean_binary_sha256']
 assert (P/(r['attempt']+'-reservation.json')).exists()
 reservation=json.loads((P/(r['attempt']+'-reservation.json')).read_text())
 assert reservation['reserved_bytes']+reservation['additional_bytes']<=reservation['limit_bytes']
 for f,h in r['source_hashes'].items():
  assert sha(d/'sources'/f)==h
  if r['exit_status']==0:sources[f]=dict(attempt=r['attempt'],sha256=h)
 if r['exit_status']==0:
  for line in r['print_axioms']:
   assert 'sorryAx' not in line
   if 'depends on axioms:' in line:
    axioms=line.split('[',1)[1].split(']',1)[0].split(', ')
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
   theorems[line.split("'")[1]]=line
 timeline.append(dict(attempt=r['attempt'],target=r['sources'][0],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=r['swaps'],source_revision=r['source_revision'],source_hashes=r['source_hashes'],dependency_fingerprint_sha256=hashlib.sha256(json.dumps(r['deps_fingerprint'],sort_keys=True).encode()).hexdigest(),print_axioms=r['print_axioms'],cgroup=r['cgroup']))
current=[]
for p in sorted((R/'lean').glob('Rc5_*.lean')):
 assert p.name in sources,p
 assert sha(p)==sources[p.name]['sha256'],p
 s=p.read_text();assert not re.search(r'^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',s,re.M),p
 nm=re.search(r'^namespace\s+([\w.]+)',s,re.M)
 for th in re.findall(r'^theorem\s+(\w+)',s,re.M):
  full=nm[1]+'.'+th;assert full in theorems,full
 current.append(dict(path=str(p.relative_to(R)),**sources[p.name]))
assert len(current)==53,len(current)
# All unmodified ledger bytes are retained verbatim.
pin=json.loads((P/'Rc5_baseline.json').read_text());ledger=R/'design/PREMISE-LEDGER-20261025.md'
assert hashlib.sha256(ledger.read_bytes()[:pin['ledger_bytes']]).hexdigest()==pin['ledger_sha256']
# Recheck inherited successful exact-ELF and production source evidence, not run it.
inherited=json.loads((R/'evidence/finish-laws-20261026/SAF_NONVACUITY.json').read_text())
rechecked=[]
for r in inherited['rows']:
 p=R/r['path'];h=sha(p);assert h==r['expected'],r['path']
 rechecked.append(dict(path=r['path'],sha256=h))
(P/'Rc5_NONVACUITY_EVIDENCE.json').write_text(json.dumps(dict(classification=inherited['classification'],new_joint_conditions='Rc5_RuntimeFixture.joint_runtime',same_cut_conditional_acceptance='Rc5_Nonrejecting.accepted_input',joint_all_retained_hypotheses='OPEN: JFx_',rows=rechecked),indent=2)+'\n')
checks=json.loads((P/'Rc5_CANONICAL_SOURCES.json').read_text())
variants=[]
for r in checks:
 if r['matches']:continue
 assert r['module'] in {'Op5T_Final','Op5T_SuccessAccepted'}
 currentText=(R/r['path']).read_text();cached=(P/('Rc5_INHERITED_'+r['module']+'.lean.txt')).read_text()
 strip=lambda s:re.sub(r'/\-.*?\-/','',s,flags=re.S)
 assert strip(currentText)==strip(cached),r['module']
 assert currentText.split('theorem accepted_pair_claims_op5',1)[1]==cached.split('theorem accepted_pair_claims_op5',1)[1]
 variants.append(dict(**r,classification='Inherited documentation-only variant; exact theorem statement and proof suffix and comment-stripped complete module equal'))
objects=json.loads((P/'Rc5_INHERITED_OBJECT_CHECKS.json').read_text());assert all(r['matches'] for r in objects)
# New work is confined to the assigned namespace/evidence plus appended ledger.
changed=subprocess.check_output(['git','diff','--name-only',pin['revision']],cwd=R,text=True).splitlines()
assert all(s.startswith('lean/Rc5_') or s.startswith('evidence/recount5-20261026/') or s=='design/PREMISE-LEDGER-20261025.md' for s in changed),changed
artifact=json.loads((R/'evidence/cp-game2-20261026/CPH_VALIDATION.json').read_text())['artifact_pins_reused']
output=dict(target='AspisR1.Rc5_Top.deployed',lean_attempts=60,lean_budget=60,kani_runs=0,kani_budget=0,passes=54,excluded_failures=sorted(failed),wall_timeouts=0,memory_kills=0,dependency_builds=0,package_replays=0,barrier_retries=0,one_own_scope_at_a_time=True,current_sources=current,theorem_axioms=theorems,standard_axioms_only=True,peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),total_wall_seconds=sum(r['wall_seconds'] for r in receipts),receipts=timeline,canonical_source_checks=len(checks),documentation_only_variants=variants,inherited_object_comparisons=len(objects),inherited_successful_source_evidence_files=len(rechecked),artifact_pins_reused=artifact,release_rebuild=False,full_joint_fixture=False,release_target_established=False,ledger_prefix_intact=True)
(P/'Rc5_validation.json').write_text(json.dumps(output,indent=2)+'\n')
(P/'Rc5_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in timeline))
print(json.dumps({k:output[k] for k in ['lean_attempts','passes','excluded_failures','current_sources','standard_axioms_only','peak_rss_kib','total_wall_seconds','canonical_source_checks','inherited_object_comparisons','inherited_successful_source_evidence_files','ledger_prefix_intact']},indent=2))
