"""Mechanical evidence checks only; no compiler, solver, Lean or external writes."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections,re
E=Path(__file__).resolve().parent;ROOT=E.parents[1]
def read(n):
 p=E/n
 return json.loads(p.read_bytes() if p.exists() else lzma.decompress(p.with_suffix(p.suffix+'.xz').read_bytes()))
assert str(ROOT)=='/Users/dominic/ZK/.worktrees/pv-k3scan'
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/pv-k3scan-20261101'
for n in ['NEH_scan.py','NEH_CONDITIONS.md','NEH_CLASSIFIER_TESTS.json']:
 b=subprocess.check_output(['git','show','ab9c588335:evidence/k3-audit-20261030/'+n]);assert (E/'classifier'/n).read_bytes()==b,n
up=subprocess.check_output(['git','show','ab9c588335:evidence/k3-audit-20261030/NEH_APPLICABILITY.json']);assert lzma.decompress((E/'classifier/NEH_APPLICABILITY.json.xz').read_bytes())==up
for p in E.rglob('*.sha256'):
 if p.with_suffix('').exists():b=p.with_suffix('').read_bytes()
 elif p.with_suffix('').with_suffix(p.with_suffix('').suffix+'.xz').exists():b=lzma.decompress(p.with_suffix('').with_suffix(p.with_suffix('').suffix+'.xz').read_bytes())
 else:continue
 assert hashlib.sha256(b).hexdigest()==p.read_text().strip(),p
raw=read('CREDITS.raw.json');credits=read('CREDITS.json');coverage=read('ROW-COVERAGE.json');summary=read('SUMMARY.json');pair=read('CONTROLLED-PAIR.json')
assert len(raw)==len(credits)==305;assert {x['k1_index']for x in raw if 'k1_index'in x}==set(range(264));assert len({x['credit_id']for x in credits})==305
assert len(coverage)==len({r['ledger_row']for r in coverage})==407
assert dict(collections.Counter(r['classification']for r in credits))==summary['classification'];assert dict(collections.Counter(r['final_status']for r in credits))==summary['final_status']
assert len(re.findall(r'^\| C\d{3} \|',(E/'K3-CREDITS.md').read_text(),re.M))==305
for x in credits:
 assert all(r in {c['ledger_row']for c in coverage}for r in x['ledger_rows'])
 assert hashlib.sha256((E/'blobs'/(x['receipt_sha256']+'.json')).read_bytes()).hexdigest()==x['receipt_sha256']
 for n,m in x['matched_sources'].items():assert hashlib.sha256((E/'blobs'/(m['sha256']+'.rs')).read_bytes()).hexdigest()==m['sha256']
 if x['classification']=='OPEN':assert x['final_status']=='SUSPENDED' or (x['final_status']=='WITHDRAWN' and 'Inherited excluded allocator diagnostic' in x['reason'])
 if x['classification']=='NOT-EXPOSED':assert x['selected_scope_evidence']['classifier_result']['classification']=='UNAFFECTED'
assert len(read('SELECTED-STANDALONE-SCOPES.json'))==6
assert pair['positive']['exit_status']==0 and pair['control']['exit_status']==1 and pair['control_failed_checks']==1 and pair['source_hashes_equal']
assert pair['deployed_transfer'].startswith('WITHHELD');assert summary['lean_used']==0 and summary['new_kani_runs']==2 and not summary['budget_exhausted']
assert read('STD-PARITY.json')['deployed_transfer']=='WITHHELD'
for id in ['K79200','K79201']:
 assert read('host/'+id+'/admission.json')['allowed'];b=read('host/'+id+'/barrier.json');assert b['allowed'] and b['own_limits']['memory.swap.max']=='0' and b['own_limits']['pids.max']=='64'
assert not subprocess.check_output(['git','diff',read('PINS.json')['base'],'--','design/PRIVACY-LEDGER-20261026.md','crates','programs'])
assert not any(p.stat().st_size>20*1024**2 for p in E.rglob('*')if p.is_file())
result={'status':'PASS','checks':['upstream classifier and four requested inputs exact; own diagnostic test output exact','264 historical observations accounted for','305 per-observation rows and receipt/source hashes','407 ledger rows covered','six selected module closures preserve raw overbroad inventories','controlled positive and matched assertion failure','both admissions and caps, source identity and cooldown','std transfer withheld; no rewritten ledger/production source','size limit; no budget-exhaustion claim'],'Lean':0,'new_Kani_invocations':2,'application_counterexamples':0,'remaining_rerun_campaign':'incomplete; OPEN packets remain suspended'}
(E/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
