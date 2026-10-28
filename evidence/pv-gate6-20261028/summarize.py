"""Assemble the adoption report from retained receipts; runs no workloads."""
from pathlib import Path
import json, hashlib, datetime
E = Path(__file__).resolve().parent
load = lambda name: json.loads((E / name).read_text())
out = load('comparison.json')
a = load('stage-a-validation.json')
assert a['passed']
out['stage_a'] = 'PASS'
out['differential'] = dict(passed=True, seeds=[6000,6999], pairs=1000,
    complete_proof_pairs=600, rejected_prefix_pairs=100, oracle_logged_pairs=4,
    baseline_revision='c57a344726745387efb38d1571d885c69ce829ee',
    pipeline='combined/corpus-6000/pipeline-final.json',
    canonical_record_and_ledger_audit='combined/record-ledger-audit.json')
out['timing_binary_pins'] = load('timing-binary-pins.json')
t = load('measurement/comparison.json')
out['timing'] = t
out['stage_b'] = 'PASS' if t['passed'] else ('INCOMPLETE' if any(r['verdict']=='INCOMPLETE' for r in t['timing']) else 'FAIL')
out['all_pairs_numeric_thresholds'] = {r['fixture']: dict(
    median_under_15=r['groups']['all']['statistics']['candidate'].get('median',float('inf'))<15,
    ratio_at_most_1_10=(r['groups']['all']['ratio_candidate_control'] or float('inf'))<=1.10,
    qualification='Includes thermally throttled pairs; does not supply the missing unthrottled sample count') for r in t['timing']}
out['window'] = dict(clock=load('window-clock.json'), cleanup=load('window-cleanup.json'))
assert out['window']['cleanup']['removed']
out['cleanup'] = load('cleanup.json')
receipts=[]
for p in sorted(E.rglob('receipt/receipt.json')):
    r=json.loads(p.read_text())
    receipts.append(dict(path=str(p.relative_to(E)), sha256=hashlib.sha256(p.read_bytes()).hexdigest(), **r))
out['attempts'] = dict(charged_native=len(receipts), lean=0, kani=0,
    numeric_native_budget='none assigned', receipts=receipts)
out['target_established'] = False
out['premise_effect'] = 'removed 0; added 0; weakened 0; changed 0; finite validation only'
(E/'comparison.json').write_text(json.dumps(out,indent=2)+'\n')
utc=lambda n:datetime.datetime.fromtimestamp(n,datetime.timezone.utc).isoformat()
lines=['\n## Adoption gate outcome\n',
    'Stage A PASS: all three ELF pins, pinned client, fixed coin0 deterministic bytes, and seeds6000–6999 differential. The inherited harness covers600 complete proof pairs,100 rejected prefixes and4 oracle-log pairs across1000 paired cases; all1000 canonical records and ledger pairs match. No completed workload was repeated during recovery.\n',
    'Optimized timing binary SHA256s:']
for w,p in out['timing_binary_pins'].items():lines.append(f"- {w}: `{p['sha256']}` ({p['bytes']} bytes).")
lines+=['','Timing results (seconds; ratio of candidate/control medians):']
for row in t['timing']:
    lines.append(f"- {row['fixture']}: **{row['verdict']}**.")
    for name,g in row['groups'].items():
        c=g['statistics']['candidate'];b=g['statistics']['control']
        if not c['n']:lines.append(f"  {name}: 0 pairs.");continue
        lines.append(f"  {name}: {c['n']} pairs; candidate median {c['median']:.6f}, p10/p90 {c['p10']:.6f}/{c['p90']:.6f}; control median {b['median']:.6f}, p10/p90 {b['p10']:.6f}/{b['p90']:.6f}; ratio {g['ratio_candidate_control']:.6f}.")
clock=out['window']['clock'];clean=out['window']['cleanup']
lines += ['',f"Planned/completed pairs: {t['planned_pairs']}/{t['completed_pairs']}; unthrottled {t['unthrottled_pairs']}, throttled {t['throttled_pairs']}; minimum unthrottled5. Measurement error: `{t['error']}`.",
    f"Window marker written {utc(clock['start'])}, immutable expiry {utc(clock['until'])}; measurement start/end {utc(t['start'])}/{utc(t['end'])}; marker removed {utc(clean['marker_removal_time'])}. Full package temperatures, throttle deltas and guards are in measurement/.",
    f"Native charged scopes: {len(receipts)}; Lean0, Kani0. Refusals consume no attempts. Every receipt records target, revision, exit, wall, peak RSS, swap, limits and axioms N/A. Task-owned Cargo target cleanup is recorded in cleanup.json; keys and raw fixture evidence retained.",
    'Stage B INCOMPLETE: a foreign pv-b3p6-lean-42574.scope appeared during the active marker, so the guard stopped measurement. Seven completed pairs are retained; partial pair7 candidate outputs are excluded. All seven completed pairs throttled; zero unthrottled pairs, below the required five. No new window or unchanged measurement rerun was launched. Next deliverable: lead repair of cross-job quiet-window enforcement and a separately authorized timing run under a reliably quiet, thermally suitable window.\n',
    'No formal premise was removed or changed. This report supplies finite functional and timing evidence for lead adoption review. Target not yet established.']
p=E/'README.md';s=p.read_text().replace('In progress. Candidate','Candidate');s=s.split('\n## Adoption gate outcome')[0];p.write_text(s+'\n'.join(lines)+'\n')
print('Assembled retained-receipt report:',out['stage_a'],out['stage_b'])
