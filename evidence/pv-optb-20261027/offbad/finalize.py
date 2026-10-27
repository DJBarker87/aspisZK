import pathlib,json,re,subprocess
P=pathlib.Path(__file__).resolve().parent
rows=[json.loads(x) for x in (P/'receipts.jsonl').read_text().splitlines()]
assert len(rows)==100 and len({r['attempt'] for r in rows})==100
assert [r['attempt'] for r in rows[-3:]]==[44897,44898,44702]
allowed={'propext','Classical.choice','Quot.sound'}
for r in rows:
 assert r['swap']=='0'
 if r['exit']==0:
  assert r['axioms'],r
  for ax in r['axioms']:
   if 'depends on axioms:' in ax:
    used=set(re.search(r'\[([^]]*)\]',ax)[1].replace(' ','').replace('\n','').split(','))
    assert used<=allowed,(r,used)
summary=dict(base='b654d6d8b176144a87a25d3dd5140f1f961a1691',branch='codex/pv-optb-20261027',audit_source_revision='8453e32be5e87d2e1f631633fa410cfc7476a06b',lean_attempts=100,lean_passes=sum(r['exit']==0 for r in rows),lean_failures=sum(r['exit']!=0 for r in rows),kani_runs=0,kani_budget=4,retired_uncharged_ids=[44620,44626,44674,44680,44694,44899],audit_attempts=rows[-3:],target_established=False,native_IndependentOffBad_proved=False,endogenous_B_headline_proved=False,native_counterexample=False,original_endpoint_premises_removed=0,trust_items_added=0,observer_changed=False,simE_changed=False,shipped_code_changed=False,shared_envJ_written=False,stopped='Lean compile budget exhausted',next_deliverable='Native reachable-state body/public-verdict synchronization off the existing union, followed by a joint real/ideal failure-aware coupling',cache_cleanup='Only assigned lean-objects cache (including read-only symlinks and hash sidecars); all four retained ledger directories and private Lean sources kept; no wallet key cleanup')
(P/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(P/'AUDIT-PIN.txt').write_text(summary['audit_source_revision']+'\n')
(P/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline',summary['base']+'..HEAD'],text=True))
text='''\n## D262 final budget and audit receipts\n\nStopped on Lean budget exhaustion: 100/100 attempts, 91 passes, 9 development\nfailures; Kani 0/4. No IDs reused. Preflight-only IDs 44620, 44626, 44674,\n44680 and 44694 were transient cgroup races; ID 44899 was an aggregate\nreservation refusal (48G + 8G > 55G). It was retired; after the prescribed\n3-minute wait, unused ID 44702 performed the final audit. No refusal was\ncharged and no barrier was bypassed.\n\nAll audit source revision: `8453e32be5e87d2e1f631633fa410cfc7476a06b`.\nModule prefix below: `R1Z/PV_OptB_OffBadAudit`.\n\n| Target suffix | ID | Exit | Wall | Peak RSS KiB | Swap |\n|---|---:|---:|---|---:|---:|\n'''
for r in rows[-3:]:text+=f"| {r['target'].split('OffBadAudit')[1]} | {r['attempt']} | {r['exit']} | {r['wall']} | {r['peak_rss_KiB']} | {r['swap']} |\n"
text+='''\nEvery audit #print axioms set is a subset of propext, Classical.choice,\nQuot.sound. Exact outputs, caps, source hashes and timings are in\n`offbad/receipts.jsonl` and its raw logs. Source and selected-object hashes\nare retained without binaries. The private compiled cache and read-only\nsymlink overlay were removed after hashing; all four task ledger directories\nand private Lean sources remain. No wallet or account key was removed.\n\nThe full native off-bad source instance and endogenous B headline are still\nopen. Original endpoint premises removed: zero. Privacy target not established.\n'''
report=P.parent/'REPORT.md';report.write_text(report.read_text()+text)
with (P.parent/'TALLY.md').open('a') as f:f.write('\nD262 continuation: 100/100 Lean (91 pass, 9 failed), Kani 0/4. Last three actual compiles are audits 44897, 44898, 44702. Historical 418xx tally above remains historical. See offbad/TALLY.md and offbad/SUMMARY.json.\n')
(P/'TALLY.md').write_text('Lean 100/100: 91 passes, 9 failures. Kani 0/4 (control-only ceiling).\nLast three actual compiles: 44897 model audit, 44898 source audit, 44702 endpoint audit.\nRetired/unlaunched: 44620, 44626, 44674, 44680, 44694, 44899. No ID reuse.\nAll IDs and full receipts: receipts.jsonl. No further Lean attempt authorized by this exhausted budget.\n')
print('Final evidence validation passed: 100 attempts, 91 pass, 9 failed, standard axioms on all passes, zero swap.')
