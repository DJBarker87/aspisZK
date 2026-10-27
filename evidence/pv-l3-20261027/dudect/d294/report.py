"""Render retained analysis without recomputing statistics or rerunning samples."""
import json,pathlib,csv,math,datetime
r=pathlib.Path(__file__).resolve().parent;d=r.parent
analysis=json.loads((r/'analysis.json').read_text());inv=json.loads((r/'raw-inventory.json').read_text());bounds=[json.loads(x) for x in (r/'window-1793111961/experiment-boundaries.jsonl').read_text().splitlines()]
families=['mask-m31','mask-qm31','mask-m31-reject','mask-qm31-reject','pole','m31-inv','qm31-inv','compress','seed-field','seed-salt','seed-field-zero','seed-salt-zero']
limits=[
'Harness only: candidate scalar sampler is inlined; no standalone instruction equivalence.',
'Harness only: candidate qm31 has actual return-register and metadata differences.',
'Harness synthetic rejection diagnostic only; scalar instruction boundary differs.',
'Harness synthetic rejection diagnostic only; qm31 return-register differences remain.',
'Valid-shape scan/return prefix matches; full symbols differ in cold panic metadata; synthetic repeated slots.',
'Nonzero arithmetic/return prefix matches; full symbols differ in cold panic metadata; zero excluded.',
'QM31::try_inv leaf matches; interval additionally includes harness wrapper/Option check and M31::inv callee; zero excluded.',
'Compressor leaf matches normalized instructions; full intervals, callers and complete prover differ.',
'Harness predicate only: candidate inlines helper; excludes OS fill, caller short circuit, retries and joint law.',
'Harness predicate only, independent salt role; excludes OS fill, caller short circuit, retries and joint law.',
'Synthetic failure diagnostic of harness predicate only; no OS, caller or retry equivalence.',
'Synthetic failure diagnostic of harness predicate only; no OS, caller or retry equivalence.']
experiments={}
with (r/'crop-results.csv').open('w') as file:
 writer=csv.writer(file,lineterminator="\n");writer.writerow(['experiment','crop_percentile','cutoff_cycles_strict','class0_n','class1_n','first_order_t','centered_square_t','max_absolute_t','threshold_crossing','conformance'])
 for family,limit in zip(families,limits):
  v=analysis.get(family)
  e=dict(instruction_attribution=limit,classes='fixed [0x35;32] seed / random seed' if family in ['mask-m31','mask-qm31'] else 'unchanged: V374-PLAN-v2.md',conformance='NON-CONFORMING: thermal abort' if v else 'NOT RUN',valid=[0,0],migrations=[0,0],threshold=4.5,tests=[],boundary_observations=[b for b in bounds if b['family']==family])
  if v:
   e.update(v);e['diagnostic_trigger']=any(abs(t)>=4.5 for s in v['tests'] for t in [s['t'],s['centered_square']['t']] if t is not None)
   e['verdict']='timing difference DETECTED in non-conforming '+('partial ' if family=='mask-qm31' else '')+'data; no qualified V374 verdict'
   e['raw_inventory']=inv['files'][family+'.csv']
   e['complete_sample_budget']=v['valid']==[1000000,1000000]
   for order in ['first_order','centered_square']:
    peak=max(((abs(s['t'] if order=='first_order' else s['centered_square']['t']),i) for i,s in enumerate(v['tests']) if (s['t'] if order=='first_order' else s['centered_square']['t']) is not None))
    value,i=peak;s=v['tests'][i];e[order+'_peak']=dict(absolute_t=value,crop_percentile='uncropped' if i==0 else 100*v['cutoff_probabilities'][i-1],cutoff_cycles=s['cutoff'],n=s['n'])
  else:
   e.update(verdict='not run; no timing verdict',complete_sample_budget=False,calibration_pooled=0)
   e['tests']=[dict(cutoff=None,n=[0,0],t=None,centered_square=dict(t=None,n=[0,0])) for i in range(101)]
  for i,s in enumerate(e['tests']):
   vals=[abs(t) for t in [s['t'],s['centered_square']['t']] if t is not None]
   s['crop_percentile']='uncropped' if i==0 else 100*(1-0.5**(10*i/100))
   s['max_absolute_t']=max(vals) if vals else None
   writer.writerow([family,s['crop_percentile'],s['cutoff'],*s['n'],s['t'],s['centered_square']['t'],s['max_absolute_t'],None if not vals else max(vals)>=4.5,e['conformance']])
  experiments[family]=e
report=dict(status='ABORTED; V374 OPEN/P; target not yet established',DOITM='OFF (V371)',source_revision='cc5fdf3956',plan='dual/V374-PLAN-v2.md amendment v2.1 LOG D294',window_created=json.loads((r/'marker-created.json').read_text()),marker_removal=json.loads((r/'marker-removal.json').read_text()),receipt=json.loads((r/'window-1793111961/receipt.json').read_text()),analysis_receipt=json.loads((r/'analysis-receipt.json').read_text()),experiments=experiments,deviations=['Boundary logger recorded 97 C at mask-m31 end and 98 C at mask-qm31 start, but only the one-second main guard enforced abort. The guard stopped sampling at 100 C; both families are non-conforming.','mask-qm31 is incomplete; last unterminated row has class/cycles/AUX/valid but missing outcome. The frozen analyzer retains its timing fields; the inventory records one unknown outcome.','SIGTERM killed the /usr/bin/time process group before its report completed; process peak RSS unavailable, cgroup peak retained.'],premises=dict(removed=[],added=[],changed=[],retained=['V374','V371','all independent privacy endpoint/deployment obligations']),next_deliverable='Lead review of thermal behavior, abort enforcement delay and threshold crossings, followed only after separate authorization and at least 30 minutes quiet-window separation by a conforming full-budget run. No second window in this job.',prior_attempts='d290/ and d293/; prior summary version retained in git b3598471ee, never pooled with these observations.')
(d/'results.json').write_text(json.dumps(report,indent=2,allow_nan=False)+'\n')
rows=[]
for f,e in experiments.items():
 if f in analysis:
  p=e['first_order_peak'];q=e['centered_square_peak'];u=e['tests'][0]
  rows.append(f"| {f} | {e['valid'][0]:,} / {e['valid'][1]:,} | {u['n'][0]:,} / {u['n'][1]:,} | {p['absolute_t']:.6f} / {q['absolute_t']:.6f} | {p['n'][0]:,} / {p['n'][1]:,} | DETECTED; non-conforming{' partial' if f=='mask-qm31' else ''} |")
 else:rows.append(f'| {f} | 0 / 0 | 0 / 0 | N/A | 0 / 0 | Not run |')
text='''# D290 / D294 — V374 v2.1 thermal abort and retained findings

**V374 remains OPEN/P. Target not yet established.** The one authorized window
aborted at package temperature **100 °C > 95 °C**. Timing differences were
**DETECTED for mask-m31 and mask-qm31, fixed versus random seed classes**, in
thermally non-conforming harness data. No fix or second window was attempted.

Amendment v2.1 was committed before marker creation in `cc5fdf3956`. The
CPU-only monitor dry test ran for 60.000020 seconds, 61 observations, exit 0,
with package readings 77–102 °C and no kernel samples or quiet marker. It
excluded iwlwifi_1/thermal_zone6 (previous ENODATA) and all other non-selected
thermal zones. See `d294/preflight.json` and `monitor-dry-test.jsonl`.

The marker was created **2026-10-27 14:39:11.703705 UTC**, with fixed expiry
**15:04:11.703705 UTC** (1500 seconds; never extended). The first drain inventory
at **14:39:11.727426 UTC** was empty. Cool-down polls were 10 seconds apart:
100 °C initially, then **72 °C at 14:39:21.751318 UTC**, satisfying the below-80
wait. Admission exited 0 with `allowed:true`. The worker used CPU 0 and the
pinned binary CPU 2; powersave/turbo-enabled/SMT-enabled/sibling 1-2 policies
matched the plan. Scope caps were 6G/8G/swap0/Tasks64. CPU identity, kernel,
ASLR, features, policies and host conditions are in
`d294/window-1793111961/host.json` and accompanying metadata.

The first CSV boundary was **14:39:22.262561 UTC**. The sampler was terminated
by the thermal guard; wrapper/scope exit 1, sampler process-group status -15.
**The trap removed the marker at 14:39:23.325512 UTC**, 11.621807 seconds after
creation, and absence was independently verified. No further window was opened.
Stream A is informed by the lead; this worker sent no messages. A further
window requires separate lead authorization and at least 30 minutes separation
(earliest separation bound **15:09:23.325512 UTC**, not an authorization).

Both binaries matched before marker creation and again at entrypoint admission:

- Harness SHA256 `ede68055604cce057f3d0b96fa575b06f30290bba4bcdb50493b7b81a797eb02`.
- Candidate SHA256 `161abfd8d155a2ccf35a461cd8e03fbf909e0f8b1c59efdddec1d76e74811472`.

No rebuild, source/kernel/class/count/threshold change, Lean or Kani run occurred.
Evidence-only monitoring copies implement the amendment; measurement remains
`taskset -c 2 .../bin/pv-dudect --measure 1000000`. Candidate source is
`73070ddd512bc4e79edfc0db714fb64dc74e87b8`; worker evidence revision is
`cc5fdf3956`. The prior summaries remain in git `b3598471ee` and raw receipts
in `d290/` and `d293/`; none of those attempts is pooled here.

## Findings and counts

Maxima below cover all preregistered crops and the uncropped test; both orders
and the entire grid are retained, without best-crop selection. Counts in the
peak column are class 0 / class 1 at the maximum (same crop for both orders).

| Experiment | Raw valid counts | Held-out uncropped counts | Max absolute t: first / centered-square | Counts at peak crop | Verdict |
|---|---:|---:|---:|---:|---|
'''+ '\n'.join(rows)+'''

For mask-m31, both maxima occur at percentile **96.875%**, strict cutoff
**338 cycles**: first-order |t| = **150.669662**, centered-square |t| =
**176.948210**. Uncropped first-order |t| = 4.001864; centered-square = 0.453668.
For partial mask-qm31, both maxima occur at percentile **98.969134%**, strict
cutoff **354 cycles**: first-order |t| = **221.701656**, centered-square |t| =
**233.473230**. Uncropped first-order |t| = 5.805023; centered-square = 0.985032.
These crossings are findings about the recorded fixed/random seed populations
in the pinned harness under this aborted environment. They do not establish
which mechanism caused the difference or a qualified shipped-prover leak.

The frozen rule is |t| < 4.5 = no leak DETECTED at this sample size, **not a
proof of absence**; |t| ≥ 4.5 = timing difference DETECTED. Neither sampled
family receives a qualified pass: both are thermally non-conforming and
mask-qm31 also lacks its full budget. The other ten have no verdict.

`results.json` retains all 101 tests per family; `d294/crop-results.csv` gives
counts, both t statistics and maximum absolute t for every crop percentile.
`d294/analysis.json` is the unmodified frozen analyzer output. The analyzer ran
once, after marker removal, in its own admitted capped scope: exit 0,
93.350087 seconds, cgroup peak 14,786,560 bytes, swap peak 0; process peak RSS
is in `d294/analysis-time.log`. Analysis and measurement were sequential.

## Deviations and resource receipts

The boundary logger observed **97 °C at mask-m31 end**, then **98 °C at
mask-qm31 start**, before the one-second main guard sampled **100 °C** and
terminated the process group. Abort enforcement was attached only to that
main guard, not to boundary observations. Consequently additional sampling
occurred after a recorded threshold exceedance. **Both affected experiments
are marked non-conforming.** This is retained as an enforcement-delay defect,
not suppressed or repaired in this job.

Boundary observations (package °C; CPU2 scaling_cur_freq in kHz):

| Family | Start | End/termination close |
|---|---|---|
| mask-m31 | 85; 3,187,931 | 97; 4,500,045 |
| mask-qm31 | 98; 4,572,574 | 94; 4,376,545 |

Boundary epochs and all coretemp inputs are retained. Start observations follow
CSV creation before warm-up; end observations follow file close (mask-qm31's
close is termination, not successful completion). These are asynchronous sensor
observations, not per-call thermal or frequency measurements. The last partial
QM31 row has complete timing/AUX/valid fields but a missing outcome: the frozen
analyzer includes its timing, while `raw-inventory.json` records one unknown
outcome. No row was edited, removed or replaced. All recorded migrations are
zero. M31 outcomes are 1,000,000 true/class; QM31 has 921,729 true class 0,
921,698 true class 1 and one unknown class-1 outcome; no recorded false results.

Worker wall 1.396695 seconds; cgroup peak **126,386,176 bytes**, swap peak 0.
Cgroup memory peak is not process peak RSS. SIGTERM killed the `/usr/bin/time`
process group before its report completed; process RSS is unavailable and
`time.log` is empty. Receipt, limits, exact target, exits and source revision
are retained in `d294/window-1793111961/receipt.json`. `#print axioms` is N/A:
no Lean. Raw CSVs remain on the host at the paths in `d294/raw-inventory.json`,
with SHA256, byte sizes and status inventories; no raw corpus or executable
is committed.

## Instruction attribution and retained obligations

**DOITM OFF (V371)** remains a substantive retained limitation under Secure Boot
lockdown. Every interval speaks directly for the pinned harness. Kernel-specific
harness-versus-candidate/shipped instruction differences limit attribution:

'''+ '\n'.join(f'- `{f}`: {limit}' for f,limit in zip(families,limits))+'''

See `INSTRUCTION-EQUIVALENCE.md` for the exact comparisons; equal leaves do not
establish complete interval, full candidate, account-route or shipped-prover
timing equivalence. Full-prover and same-public valid-witness obligations remain.
No premise was removed, added, weakened or moved into T; V374, V371 and every
independent privacy endpoint/deployment premise remain retained.

Next deliverable: lead review of thermal behavior, the abort-enforcement delay,
and both threshold crossings; then a separately authorized conforming full-budget
measurement after the required separation. No further measurement in this job.
'''
(d/'RESULTS.md').write_text(text)
