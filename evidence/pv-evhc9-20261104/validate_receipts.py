from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((E/'lean-92070/receipt.json').read_text());assert r['exit_status']==0 and str(r['swaps'])=='0'
assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for n,h in r['source_hashes'].items():assert sha(E/'lean-92070/sources'/n)==h==sha(E/n),n
for n in ['NEP_WALKER','NEP_Planted','NEP_Mutations']:
 assert (E/(n+'.lean')).read_bytes()==(E/'inputs'/(n+'.lean')).read_bytes()
old=(E/'inputs/NEP_Driver.lean').read_text();new=(E/'NEP_Driver.lean').read_text()
def strip(s):return s[:s.index('  let (modules, roots) :=')]+s[s.index('  let env ←'):]
assert strip(old)==strip(new)
steps=json.loads((E/'PREFLIGHT-STEPS.json').read_text());assert len(steps)==7
assert all(s['exit_status']==s['expected_exit'] and str(s['swaps'])=='0' for s in steps)
p=json.loads((E/'PREFLIGHT-RESULT.json').read_text());assert p['status']=='PASS' and len(p['fixture_results'])==10
for row in p['fixture_results']:
 names=(E/('NEP_fixtures_'+row['root']+'_REACHABLE.txt')).read_text().splitlines()
 assert len(set(names))==len(names)==row['reachable_constants'] and row['equal']
 assert row['walked_axioms']==row['collect_axioms']
 assert sorted(row['walked_axioms'])==row['walked_axioms']
assert len(p['missing_constant_control'])==1 and not p['missing_constant_control'][0]['complete']
a=json.loads((E/'admission-92070-0.json').read_text());assert a['allowed'] is True
assert json.loads((E/'LAUNCH-RESULT.json').read_text())['exit_status']==0
recovered=[]
for f in (E/'recovered-evhc7').glob('lean-*/receipt.json'):
 v=json.loads(f.read_text())
 for n,h in v['source_hashes'].items():assert sha(f.parent/'sources'/n)==h
 recovered.append({'attempt':v['attempt'],'exit_status':v['exit_status']})
# The aggregate runner captures only the sequence's stdout; full summary lines live in each step log.
summary=dict(status='PASS',attempt=92070,preflight_budget_used=1,preflight_budget_remaining=0,source_revision=r['source_revision'],scope_exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],limits=r['limits'],original_NEP_cases=8,extra_positive_cases=2,expected_negative_cases=1,walker_byte_identical=True,driver_non_name_code_identical=True,recovered_evhc7=recovered,print_axioms=[s for row in steps for s in row['print_axioms']],print_axioms_note='Summary based. Full lines retained per step; raw walks separately in PREFLIGHT-RESULT.json and fixtures.log. Planted test axioms are intentional controls, not release axioms.',agg16_admissions_requested=0,agg16_scopes_started=0,full_composition_audit='NOT_RUN',research_revision=subprocess.check_output(['git','rev-parse','research'],text=True).strip())
(E/'RECEIPT-VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print('Validated one normal scope, 10 successful cases, one expected hard error; no release audit.')
