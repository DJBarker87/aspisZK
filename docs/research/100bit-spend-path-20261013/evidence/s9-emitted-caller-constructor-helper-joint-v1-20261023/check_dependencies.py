from pathlib import Path
import hashlib,json,re,subprocess,sys
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();allowed={'propext','Classical.choice','Quot.sound'}
for d in m['coherent_dependency_checks']:
 p=r/d['receipt'];x=json.loads(p.read_text());assert x['exit_status']==0 and x['process_swaps']==0;assert x['source_sha256']==d['source_sha256'] and x['object_sha256']==d['object_sha256'];assert sha(r/d['source_path'])==d['source_sha256']
 log=p.with_name('lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 reports=re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S)
 assert reports or 'does not depend on any axioms' in log
 for report in reports:assert {x.strip() for x in report.split(',') if x.strip()}<=allowed,report
for name in m['source_dependencies']:assert (r.parent/name/'manifest.json').is_file(),name
assert not m['release_wide_replay_claim'] and not m['full_pair_caller_closed']
subprocess.run([sys.executable,str(r/'check_emitted_source.py')],check=True)
print('PASS: coherent focused caller dependencies and standard axioms; explicit producer/helper/source-runtime boundaries preserved')
