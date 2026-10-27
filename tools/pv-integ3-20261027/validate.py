from pathlib import Path
import json,ast,re,subprocess,hashlib,shutil
E=Path('evidence/pv-integ1-20261027/d298');T=Path('tools/pv-integ3-20261027')
checks={}
elf=json.loads((E/'elf-summary.json').read_text());checks['all_elf_pins']=all(r['matches'] and r['sha256']==r['expected'] for r in elf.values())
client=json.loads((E/'client-summary.json').read_text());checks['client_routes']=client['generate_for_mask_nonce_reachable'] and client['op223_compress_tagged_tuple_reachable']
fixture=json.loads((E/'fixture-comparison.json').read_text());checks['deterministic_fixture_gate']=fixture['passed'];checks['only_diagnostic_seconds_differ']=all(set(r['raw_result_differing_fields'])=={'seconds'} for r in fixture['comparisons'])
checks['source_identity']=all(json.loads((E/f).read_text())['passed'] for f in ['source-identity.json','baseline-source-identity.json'])
lean=json.loads((E/'lean-source-assessment.json').read_text());checks['no_invalidated_imports']=not lean['recompile_required'] and not lean['changed_imported_sources'];checks['no_lean_or_kani_attempts']=lean['lean_attempts']==lean['kani_attempts']==0
cleanup=json.loads((E/'cleanup.json').read_text());checks['cargo_targets_removed_keys_retained']=not cleanup['remaining_cargo_targets'] and cleanup['keys_destroyed']==0 and len(cleanup['retained_keys'])==3
receipts=[]
for p in E.glob('**/receipt/receipt.json'):
 r=json.loads(p.read_text());lim=r['limits'];assert lim=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},p
 assert r['swaps']==0,p
 if r['exit_status']!=0:assert 'build-pool-executable-wrapper-reservation-02' in str(p) and r['exit_status']==1,p
 receipts.append(dict(receipt=str(p),source_revision=r['source_revision'],target=r['command'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],print_axioms=r['print_axioms']))
checks['capped_receipts']=len(receipts)==10
for p in T.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
for block in re.findall(r'```sh\n(.*?)```',(E/'COMBINED-PLAN.md').read_text(),re.S):subprocess.run(['bash','-n'],input=block,text=True,check=True)
checks['planned_script_syntax_only']=True
changes=subprocess.check_output(['git','diff','--name-only','9ff5a4594e','--','crates','programs','*.lean','Cargo.toml','Cargo.lock'],text=True);checks['no_implementation_or_proof_edits']=not changes
no_runs=subprocess.run(['ssh','dombarker@100.108.41.90','test ! -e /home/dombarker/project-offloads/codex-pv-integ1-20261027/d298/combined']).returncode==0;checks['combined_gates_not_executed']=no_runs
for p in T.glob('__pycache__'):shutil.rmtree(p)
report=dict(source_revision='9ff5a4594ec1cad5b5d12c7cb5a49270f9b098e3',checks=checks,all_checks_passed=all(checks.values()),literal_raw_result_json_passed=fixture['literal_raw_result_json_passed'],host_receipts=receipts,headline_premises_removed=0,formal_target_established=False)
(E/'validation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='host_receipts'},indent=2));assert report['all_checks_passed']
