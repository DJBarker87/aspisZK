from pathlib import Path
import json,hashlib,ast,subprocess
B=Path(__file__).resolve().parent
ROOT=B.parent.parent
errors=[]
def check(ok,label):
 if not ok:errors.append(label)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
receipts=[]
for name in [f'XRg_{i:03d}' for i in range(1,13)]+[f'XRg_K{i:03d}' for i in range(1,11)]:
 d=B/name;r=json.loads((d/'receipt.json').read_text());receipts.append(r)
 check(r['attempt']==name,'attempt '+name)
 check(r['limits']==limits,'limits '+name)
 check(r['swaps']=='0','swap '+name)
 check(r['reservation_retries']==0,'retries '+name)
 check(r['source_revision'] and r['deps_fingerprint'],'pins '+name)
 check(r['print_axioms'].startswith('N/A:'),'axiom applicability '+name)
 expected=2 if name in ['XRg_002','XRg_005','XRg_007','XRg_009','XRg_011'] else 0
 check(r['exit_status']==expected,'exit '+name)
 admission=json.loads((B/(name+'-reservation.json')).read_text());check(admission['allowed'],'admission '+name)
 for f,h in r['source_hashes'].items():
  check(sha(d/'sources'/f)==h,'snapshot '+name+'/'+f)
  check(sha(B/f)==h,'current source '+name+'/'+f)
 log=(d/'stdout.log').read_text()
 check('CBMC timed out' not in log and r['exit_status'] not in [124,137],'timeout/kill '+name)
 if name.startswith('XRg_K'):
  check('VERIFICATION:- SUCCESSFUL' in log and '1 successfully verified harnesses, 0 failures' in log,'Kani success '+name)
  check(r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3','optimized '+name)
  check(r['env']['CARGO_BUILD_JOBS']=='1','compiler jobs '+name)
base=json.loads((ROOT/'evidence/extraction-repro6-20261027/XRf_kit.json').read_text())
expected={r['idents'] for r in base['explicit_release_opaque_leaves']}
adds=['aspis_r1_cost_probe::r1_semantic::claims','aspis_r1_cost_probe::r1_wire::decode_k','aspis_r1_cost_probe::r1_wire::validate_record_fields','aspis_r1_cost_probe::r1_semantic::semantic_boundary','aspis_r1_cost_probe::fast_pairing::canonical::push','aspis_r1_cost_probe::sampler::circle_sample::call_once']
inv=[]
for i,count in enumerate([1,1,2,3,4,5,6],1):
 stem=f'XRg_{i:02d}_release_candidate'
 v=json.loads((B/(stem+'_tx1_inventory.json')).read_text());r=json.loads((B/(stem+'_charon_result.json')).read_text())
 check(v['ready_for_aeneas'] and not v['missing_callees'],'closure '+stem)
 check(v['sha256']==r['llbc_sha256'] and v['bytes']==r['llbc_bytes'],'LLBC pins '+stem)
 check(r['exit']==0 and r['llbc_has_errors'] is False,'Charon valid '+stem)
 check({x['idents'] for x in v['release_opaque']}==expected|set(adds[:count]),'exact leaves '+stem)
 check(not json.loads((B/f'XRg_{i:02d}_release_input_check.json').read_text())['errors'],'source audit '+stem)
 inv.append({'generation':i,'sha256':v['sha256'],'leaves':len(v['release_opaque']),'calls':sum(len(f['callees']) for f in v['functions'])})
for p in B.glob('XRg_*.py'):ast.parse(p.read_text());
a=json.loads((B/'XRg_HostAudit.json').read_text());old=json.loads((ROOT/'evidence/extraction-repro6-20261027/XRf_HostAudit.json').read_text())
check(a['files_checked']==7978 and not a['changed_source_files'],'final release source audit')
check(not a['generated_outputs'],'no complete output')
check(a['runner_matches_coherent'],'unchanged coherent runner')
check({r['path']:r['sha256'] for r in a['tools']}=={r['path']:r['sha256'] for r in old['tools']},'tool pins unchanged')
for r in a['receipts']:
 p=B/r['attempt']
 check(sha(p/'receipt.json')==r['receipt']['sha256'],'host receipt '+r['attempt'])
 check(sha(p/'stdout.log')==r['stdout']['sha256'],'host stdout '+r['attempt'])
check(len(a['receipts'])==22,'host receipt count')
recount=json.loads((B/'XRg_recount.json').read_text())
check(sha(ROOT/'lean/Rc10_Top.lean')==recount['before_top_sha256']==sha(B/'XRg_Top.BEFORE.lean.txt')==sha(B/'XRg_Top.AFTER.lean.txt'),'actual top identical')
check(sha(ROOT/recount['ledger_path'])==recount['ledger_sha256'],'ledger unchanged')
clean=json.loads((B/'XRg_Cleanup.json').read_text());check(not clean['live_own_provers'],'no live own prover')
changed=subprocess.check_output(['git','diff','--name-only','8c3896b89a^'],cwd=ROOT,text=True).splitlines()
check(all(p.startswith('evidence/extraction-repro7-20261027/') for p in changed),'mutation scope')
report={'errors':errors,'attempts':len(receipts),'extraction':12,'charon':7,'aeneas':5,'kani':10,'kani_pass':10,'lean':0,'wall_seconds_total':sum(r['wall_seconds'] for r in receipts),'max_rss_kib':max(int(r['peak_rss_kib']) for r in receipts),'max_cgroup_peak_bytes':max(int(r['cgroup_memory_peak_bytes']) for r in receipts),'swaps':0,'limits':limits,'generations':inv,'top_recount_delta':{'T':0,'P':0,'G':0,'C':0},'nonvacuity':'local bounded witnesses only; joint actual-top inhabitant OPEN','new_top_axioms':'N/A: no new Lean theorem','target_established':False}
(B/'XRg_Verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2));raise SystemExit(bool(errors))
