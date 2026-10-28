from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
R=Path(__file__).resolve().parent;E=R.parent
read=lambda p:json.loads(p.read_text())
s=read(R/'measurement/comparison.json');pre=read(R/'preflight.json');clock=read(R/'window-clock.json');rem=read(R/'measurement-marker-removal.json');receipt=read(R/'measurement-scope/receipt/receipt.json');val=read(R/'validation.json')
assert val['validated']
x=read(E/'comparison.json');assert 'd358' not in x
stage_a_keys=['candidate_revision','stage_a','elf_pins','client','fixed_fixture','differential','stage_a_validation']
stage_a_digest=hashlib.sha256(json.dumps({k:x[k] for k in stage_a_keys},sort_keys=True).encode()).hexdigest()
old={k:x[k] for k in ['stage_b','timing','window','all_pairs_numeric_thresholds']}
x['previous_stage_b_windows']=[dict(log='D350',qualification='Seven throttled pairs retained as evidence only; no verdict.',**old)]
x['stage_b']='PASS' if s['passed'] else ('FAIL' if any(t['verdict']=='FAIL' for t in s['timing']) else 'UNDECIDED')
x['timing']=s;x['window']=dict(clock=clock,cleanup=rem,trap=read(R/'window-cleanup.json'));x.pop('all_pairs_numeric_thresholds',None)
x['d358']=dict(preflight=pre,validation='resume-d358/validation.json',stage_a_reused=True,stage_a_evidence_digest=stage_a_digest,authorized_new_windows=1,new_windows_executed=1,planned_valid_unthrottled_pairs=10,measurement_receipt='resume-d358/measurement-scope/receipt/receipt.json',keys_deleted=0,keys_moved=0,cargo_targets_created=0)
x['attempts']['charged_native']+=1
x['attempts']['receipts'].append(dict(path='resume-d358/measurement-scope/receipt/receipt.json',sha256=hashlib.sha256((R/'measurement-scope/receipt/receipt.json').read_bytes()).hexdigest(),**receipt))
(E/'comparison.json').write_text(json.dumps(x,indent=2)+'\n')
utc=lambda t:datetime.fromtimestamp(t,timezone.utc).isoformat()
lines=['## D358 resumed Stage B: '+x['stage_b'],'',f"Exactly one new window; {s['completed_pairs']}/10 pairs completed, {s['valid_pairs']} valid, {s['invalid_pairs']} invalid, {s['throttled_pairs']} throttled, **{s['valid_unthrottled_pairs']}/10 valid and unthrottled**. The D358 gate requires the full planned count of ten valid, unthrottled pairs. The first window’s seven throttled pairs remain separate historical evidence.",'',f"Window marker written **{utc(clock['start'])}**, immutable expiry {utc(clock['until'])}. Measurement **{utc(s['start'])}–{utc(s['end'])}**. Marker removed **{utc(rem['marker_removal_time'])}**, {val['marker_removal_delay_seconds']:.6f}s after measurement ended. Drain {read(R/'drain-complete.json')['seconds']:.6f}s. No marker extension. Immediate deletion is recorded in `measurement-marker-removal.json`; the subsequent fallback trap found it already absent.",'','| Fixture / sample | n | Candidate median (p10–p90), s | Control median (p10–p90), s | Candidate/control |','|---|---:|---:|---:|---:|']
for t in s['timing']:
 for name in ['all','valid_unthrottled','valid_throttled','invalid']:
  g=t['groups'][name];c=g['statistics']['candidate'];b=g['statistics']['control'];n=c['n']
  cell=lambda v:f"{v['median']:.6f} ({v['p10']:.6f}–{v['p90']:.6f})" if v['n'] else 'unavailable'
  ratio=f"{g['ratio_candidate_control']:.6f}" if n else 'unavailable'
  lines.append(f"| {t['fixture']} / {name} | {n} | {cell(c)} | {cell(b)} | {ratio} |")
lines+=['','Per-pair thermal telemetry (maximum package temperature, and maximum per-CPU counter increment; package counters may be repeated across CPUs):','','| Pair (coin) | Package °C before → after | Package throttle count Δ | Core throttle count Δ | Valid |','|---|---:|---:|---:|---|']
for pair in read(R/'measurement/pairs.json'):
 i=pair['pair'];before=read(R/f'measurement/pair-{i}-before.json');after=read(R/f'measurement/pair-{i}-after.json');delta=pair['thermal_counter_deltas']
 temp=lambda x:max(x['package_temperatures_millidegrees'].values())/1000
 count=lambda name:max((v for k,v in delta.items() if k.endswith('/'+name)),default=0)
 lines.append(f"| {i+1} ({pair['coin']}) | {temp(before):.1f} → {temp(after):.1f} | {count('package_throttle_count')} | {count('core_throttle_count')} | {pair['valid']} |")
lines+=['',f"Transfer: **{s['timing'][0]['verdict']}**. Withdrawal: **{s['timing'][1]['verdict']}**. Throttled or invalid pairs do not supply a gate verdict. Stop reason: {s['stop_reason'] or s['error'] or 'planned measurement complete'}. No additional window launched.",'',f"Shared reservation.py verified before the marker: `{pre['scanner_sha256']}` (lead’s D358 repair, candidate 508dfb9230). Optimized binary hashes rechecked: control `{pre['binaries']['control']['sha256']}`, candidate `{pre['binaries']['candidate']['sha256']}`. Both match retained build pins; no rebuild, compilation, Lean or Kani. Stage A PASS on 82566acdfb is reused unchanged, including three ELF pins, pinned client, fixed fixtures and 1,000/1,000 differential.",'',f"Each pair alternates control/candidate order, pins CPU affinity to 0–21, and records package temperature and throttle counters before/after. Running cx-/pv- scopes and every other capped user job are inventoried before each pair and each side, and after each side ({val['guard_snapshots']} retained snapshots); any intrusion marks the pair INVALID, with stopping only after three consecutive invalid pairs. Proof/public bytes, canonical results (seconds excluded) and ledger files match within every completed pair on both fixtures.",'',f"New measurement scope receipt: exit {receipt['exit_status']}, wall {receipt['wall_seconds']}s, peak RSS {receipt['peak_rss_kib']}KiB, swaps {receipt['swaps']}, cgroup peak {receipt['cgroup_memory_peak_bytes']} bytes; MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; candidate revision 82566acdfb488183022f41ac564c11df22c9404f; #print axioms N/A (native measurement). Full receipts, telemetry, guard inventories, transport retries and independent statistics validation: `resume-d358/`.",'','No Cargo targets were created; previous task-target cleanup stands. No key cleanup or movement; keys and raw proof evidence remain securely on the host. Premises before/after unchanged: removed0, retained substantive obligations, added0, weakened0, changed0. T remains entropy_law, entropy_kernel, observation. Target not yet established. Next deliverable: lead review of the thermal evidence and a separately authorized way to obtain the full valid, unthrottled cohort.','', '---','','The report below records Stage A and the original D350 window; its partial timing verdict is historical.','']
p=E/'README.md';text=p.read_text();text=text.replace('## Adoption gate outcome','## First-window historical outcome (D350)')
first,rest=text.split('\n',1);p.write_text(first+'\n\n'+'\n'.join(lines)+'\n'+rest.lstrip('\n'))
print(json.dumps(dict(stage_b=x['stage_b'],counts={k:s[k] for k in ['completed_pairs','valid_pairs','invalid_pairs','valid_unthrottled_pairs','throttled_pairs']},window_start=utc(clock['start']),measurement_end=utc(s['end']),marker_removal=utc(rem['marker_removal_time'])),indent=2))
