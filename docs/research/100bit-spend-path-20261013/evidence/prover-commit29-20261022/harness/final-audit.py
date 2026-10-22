from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent;L=Path('docs/research/v8-r0-zk-20261009/lean')
allowed={'propext','Classical.choice','Quot.sound'}
a=(E/'lean/out-7867.log').read_text()
assert re.search(r'^exit=0$',a,re.M)
lines=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",a,re.S)
assert len(lines)==26,len(lines)
for line in lines:
 if 'depends on axioms:' in line:
  atoms=set(re.search(r'\[([^\]]*)\]',line)[1].replace('\n','').replace(' ','').split(','))-{''}
  assert atoms<=allowed,line
modules=['FieldsSource29','Fields29','StepSource29','Step29','Rows29','Walk29','29Audit']
for module in modules:
 p=L/'R1Z'/('ProverCommit'+module+'.lean');s=p.read_text()
 code=re.sub(r'/-.*?-/', '',s,flags=re.S);code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',code),p
 assert 'set_option maxRecDepth' not in s and 'set_option maxHeartbeats' not in s,p
for name in ['iteration29-row0-empty-v2','iteration29-row2-root-v1']:
 r=json.loads((E/'receipts'/name/'receipt.json').read_text());assert r['exit_status']==0
 assert 'VERIFICATION:- SUCCESSFUL' in (E/'receipts'/name/'stdout.log').read_text()
for name in ['iteration29-row15-v1','iteration29-row14-fueled-v1']:
 r=json.loads((E/'receipts'/name/'receipt.json').read_text());assert r['exit_status']==124
elf=json.loads((E/'frozen-elf-final-check.json').read_text())
assert set(elf['programs'])=={'default','devnet','pool'}
for x in elf['programs'].values():assert x['byte_identical'] and x['cmp_exit']==0 and x['sha256']==x['expected_sha256'] and x['receipt']['exit_status']==0
pins=json.loads((E/'frozen-source-inventory.json').read_text());assert not pins['result']['differences']
for name,want in pins['pins'].items():assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==want['sha256'],name
closure=json.loads((E/'closure-check.json').read_text());assert closure['audit_attempt']==7867 and not closure['object_differences'] and closure['local_sources_match']
endpoint=json.loads((E/'endpoint/identity.json').read_text());assert endpoint['premises_removed']==0 and endpoint['byte_identical']
p=Path(endpoint['source']);assert hashlib.sha256(p.read_bytes()).hexdigest()==endpoint['sha256']
for name in ['before','after']:assert (E/'endpoint'/(name+'.lean.txt')).read_bytes()==p.read_bytes()
for job in ['fields29-v1','iteration29-v1']:
 x=json.loads((E/(job+'-llbc.json')).read_text());assert x['has_errors'] is False and x['opaque']==[]
status=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),audit_attempt=7867,axiom_lines=26,accepted_axioms=sorted(allowed),new_theorems=21,import_objects=closure['checked_import_objects'],shipped_files=pins['result']['checked_files'],all_three_frozen_elfs_byte_identical=True,completed_native_error_preflight='row 0 empty record',completed_native_success_error_preflight='row 2 root record, <=37 bytes',native_semantic_iteration_gate='NOT ESTABLISHED: row 14 fueled and row 15 timed out',native_walk_join=False,shippedProverExperiment=False,whole_run_joins=False,refinement_premises_removed=0,target_established=False,no_full_manifest_replayed='native source preflight incomplete')
(E/'final-audit.json').write_text(json.dumps(status,indent=2)+'\n');print(json.dumps(status,indent=2))
