from pathlib import Path
import json,re,hashlib,collections,subprocess
E=Path(__file__).resolve().parent
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
expected='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
rows=[]
for p in sorted(E.glob('NBZ_K*/receipt.json')):
 r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();a=r['attempt'];h=r['command'][r['command'].index('--harness')+1];negative=h.endswith('_negative')
 if r['exit_status']==0:status='DIAGNOSTIC_PASS' if '::NBZ_observer::' in h else 'LOCAL_RESTRICTED_PASS' if h=='verifier::candidate::NBZ_dictionary::NBZ_line' else 'LOCAL_PASS'
 elif 'CBMC timed out' in log or r['exit_status']==124:status='TIMEOUT'
 elif 'Failed Checks:' in log:status='EXPECTED_NEGATIVE_FAIL' if negative else 'POSITIVE_FINDING_FAIL'
 elif 'compilation error' in log or 'could not compile' in log:status='COMPILE_FAILURE'
 elif 'CBMC failed with status 15' in log:status='STOPPED_REDUNDANT_CONTROL'
 else:status='EXCLUDED_OTHER'
 assert not (negative and r['exit_status']==0),'VACUOUS CONTROL '+a
 assert r['limits']==limits and str(r['swaps'])=='0'
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert r['source_hashes']['NBZ_src/Cargo.lock']==expected
 assert r['source_hashes']['NBZ_src/crates/aspis-r1-cost-probe/src/KMX_stubs.rs']=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
 graph=json.loads((E/(a+'-graph-check.json')).read_text());assert graph['exact_frozen_resolved_graph_match'] and graph['lock_unchanged'] and graph['lock_after_sha256']==expected
 meta=json.loads((E/graph['metadata_receipt']).read_text());assert meta['exit_status']==0
 reservation=json.loads((E/(a+'-reservation.json')).read_text());assert reservation['allowed'] is True
 rows.append(dict(attempt=a,harness=h,status=status,negative=negative,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),swaps=int(r['swaps']),source_revision=r['source_revision'],source_hashes=r['source_hashes'],graph_check=a+'-graph-check.json',receipt=a+'/receipt.json'))
assert len(rows)==90,(len(rows),'Kani not terminal/exhausted')
lean=[]
for p in sorted(E.glob('NBZ_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());assert r['limits']==limits and str(r['swaps'])=='0';lean.append(r)
assert len(lean)==13
rc=json.loads((E/'NBZ_L013/receipt.json').read_text());assert rc['exit_status']==0 and len(rc['print_axioms'])==20
for line in rc['print_axioms']:
 ax=re.search(r'axioms: \[([^]]*)\]',line)
 assert ax and set(x.strip() for x in ax.group(1).split(',')) <= {'propext','Classical.choice','Quot.sound'},line
source_checks=[]
for module,attempt in [('NBZ_Carrier','NBZ_L004'),('NBZ_Wide','NBZ_L002'),('NBZ_Folds','NBZ_L005'),('NBZ_WordFrame','NBZ_L007'),('NBZ_Nested','NBZ_L010'),('NBZ_DotBounds','NBZ_L008'),('NBZ_DotPhase','NBZ_L009'),('NBZ_DotStages','NBZ_L012'),('NBZ_Audit','NBZ_L013')]:
 p=Path('docs/research/100bit-spend-path-20261013/lean')/(module+'.lean');r=json.loads((E/attempt/'receipt.json').read_text());sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==r['source_hashes']['NBZ_generated/'+module+'.lean']
 source_checks.append(dict(module=module,accepted=attempt,sha256=sha))
positives=[r for r in rows if r['status'] in ['LOCAL_PASS','LOCAL_RESTRICTED_PASS']];paired=[]
for row in positives:
 neg=next((r for r in rows if r['harness']==row['harness']+'_negative' and r['status']=='EXPECTED_NEGATIVE_FAIL'),None);assert neg,row['attempt'];paired.append(dict(positive=row['attempt'],negative=neg['attempt'],harness=row['harness']))
ledger=[json.loads(l) for l in (E/'NBZ_ATTEMPTS.jsonl').read_text().splitlines()];assert len({r['attempt'] for r in ledger})==len(ledger)
assert {r['attempt'] for r in ledger if r['kind']=='kani'}=={r['attempt'] for r in rows}
summary=dict(status='OPEN; target not yet established',branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),frozen_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',kani_used=90,kani_limit=90,kani_status_counts=dict(collections.Counter(r['status'] for r in rows)),lean_used=13,lean_limit=50,lean_passes=sum(r['exit_status']==0 for r in lean),public_top_theorems=20,private_helpers_audited=2,accepted_axioms=['propext','Classical.choice','Quot.sound'],max_kani_rss_kib=max(r['peak_rss_kib'] for r in rows),all_swaps_zero=True,all_frozen_graphs_match=True,all_locks_unchanged=True,no_false_expectation_control_passed=True,paired_new_local_passes=paired,accepted_source_checks=source_checks,axioms_audit='NBZ_L013/receipt.json',source_elf_rebuilt=False,shipped_source_changed=False,push=False)
(E/'NBZ_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'NBZ_RUNS.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'NBZ_RUNS.md').write_text('# Actual Kani attempts\n\n| Attempt | Status | Wall s | RSS KiB | Target |\n|---|---|---|---|---|\n'+''.join(f"| {r['attempt']} | {r['status']} | {r['wall_seconds']:.3f} | {r['peak_rss_kib']} | `{r['harness']}` |\n" for r in rows)+'\nAll exact commands, source revisions/hashes, dependencies, cgroup limits, swap and outputs are in the linked per-attempt directories/configurations and NBZ_ATTEMPTS.jsonl. No .olean, binary, ELF or archive is committed.\n')
(E/'NBZ_BUDGET_DISPOSITION.json').write_text(json.dumps(dict(actual_kani_invocations=90,limit=90,lean_compiles=13,lean_limit=50,no_remaining_lean_only_obligation='Model/window/domain induction and same-writer model already proved; every remaining internal row needs native/call-site or actual library/source association, listed individually in NBZ_query_BRIDGE.md'),indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['kani_used','kani_status_counts','lean_used','public_top_theorems','max_kani_rss_kib']}))
