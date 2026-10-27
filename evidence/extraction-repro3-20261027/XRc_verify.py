from pathlib import Path
import json,hashlib,subprocess
B=Path(__file__).resolve().parent;R=B.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for name in ['XRc_001','XRc_002','XRc_003','XRc_L001']:
 j=json.loads((B/name/'receipt.json').read_text())
 assert j['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for p,h in j['source_hashes'].items():
  assert sha(B/name/'sources'/p)==h
  assert sha(B/p)==h
 reservation=json.loads((B/f'{name}-reservation.json').read_text())
 assert reservation['allowed'] and reservation['all_populated_scopes_bounded']
 assert j['swaps']=='0' and j['exit_status'] not in [124,137]
 rows.append({k:j[k] for k in ['attempt','kind','command','source_revision','source_tree_dirty','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']})
assert rows[-1]['print_axioms']==["'XRc_Association.verifier_error_association' does not depend on any axioms"]
assert '-M7000' in rows[-1]['command']
for tag in ['BEFORE','AFTER']:
 assert (B/f'XRc_Top.{tag}.lean.txt').read_bytes()==(R/'lean/Rc10_Top.lean').read_bytes()
recount=json.loads((B/'XRc_recount.json').read_text())
assert sha(R/'design/PREMISE-LEDGER-20261025.md')==recount['ledger_sha256']
raw=json.loads((B/'XRc_four_leaves_outputs.json').read_text())
for r in raw['outputs']:
 n=Path(r['path']).name
 if n!='translation.json':
  p=B/('XRc_INCOMPLETE_'+n+'.txt')
  assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
slicej=json.loads((B/'XRc_ErrorSlice.json').read_text())
s=(B/'XRc_INCOMPLETE_Types.lean.txt').read_text();a=s.index('@[discriminant isize]\ninductive verifier.Error');z=s.index('\n\n',a);block=s[a:z]
assert hashlib.sha256(block.encode()).hexdigest()==slicej['exact_declaration_sha256']
assert 'namespace XRc_Release\n'+block+'\nend XRc_Release' in (B/'XRc_Association.lean').read_text()
changed=subprocess.check_output(['git','diff','--name-only','8b06d01154257c4bce1508970a15e5a8d3ab56fb'],cwd=R,text=True).splitlines()
assert all(p.startswith('evidence/extraction-repro3-20261027/') for p in changed)
module=(B/'XRc_Association.lean').read_text()
assert not any(w in module for w in ['sorry','admit','native_decide','maxHeartbeats','maxRecDepth'])
assert not any(line.startswith('axiom ') for line in module.splitlines())
assert not any('import XRc_' in p.read_text(errors='replace') for p in (R/'lean').glob('*.lean'))
host=json.loads((B/'XRc_HostAudit.json').read_text())
assert host['runner_unchanged'] and not host['release_source_errors']
assert all(r['match'] for r in host['retained_artifact_checks'])
summary={'attempts':rows,'used':{'Charon':0,'Aeneas':3,'Lean':1,'Kani':0},'limits':{'Charon_Aeneas':6,'Lean':100,'Kani':0},'boundary_bisections_used':2,'budget_exhausted':False,'no_unchanged_retry_or_timeout_or_memory_kill':True,'checks_passed':True,'top_and_ledger_unchanged':True,'module_not_imported_by_top':True,'exact_error_declaration_slice':True,'raw_output_hashes_match':True,'only_job_evidence_changed':True,'incomplete_kit':True,'full_typed_association':False,'pending_missing_body_clarification':True}
(B/'XRc_Verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='attempts'},indent=2))
