"""Finalize evidence after all authorized gates; performs no compilation."""
from pathlib import Path
import json,subprocess,sys
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026';toolsdir=Path(__file__).resolve().parent
t=json.loads((ev/'RESUME5-TALLY.json').read_text());assert t['lean_charged']==100 and t['kani_charged']==12
assert all(x['state']=='complete' for x in t['kani_runs'])
for run in t['kani_runs']:
 c=json.loads((ev/run['name']/'cleanup.json').read_text());assert c.get('scope_absent_or_empty') or (c.get('scope_exists_after') is False and not c.get('processes_after'))
for script in ['resume5_summary.py','resume5_receipts_index.py']:
 subprocess.run([sys.executable,str(toolsdir/script)],check=True)
log=subprocess.check_output(['git','log','--oneline','148ce95eec..HEAD'],cwd=root,text=True)
(ev/'RESUME5-COMMITS.txt').write_text('git log --oneline 148ce95eec..HEAD\n'+log)
counts=json.loads((ev/'RESUME5-COUNTS.json').read_text())
verdicts=[]
for run in t['kani_runs']:
 r=json.loads((ev/run['name']/'collected-receipt.json').read_text());verdicts.append({'harness':run['harness'],'exit':r['exit'],'wall':r['wall']})
finished=dict(branch=subprocess.check_output(['git','branch','--show-current'],cwd=root,text=True).strip(),starting_revision='148ce95eec',evidence_revision_before_final_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),counts=counts,kani=verdicts,op223_source='OPEN; stable theorem absent',V164_hypotheses_before_after='P_source_p6, P_proof_bytes, reservation unchanged; exact before/after source/hash snapshots retained',endpoint_premises_removed=0,candidate_rows='23/73 unchanged',next_deliverable='Transparent validated shipped-compressor extraction or native canonical16 agreement plus complete reachable producer/consumer association, yielding the exact stable op223 source boundary; unrestricted V164 equality remains explicitly open',stop_reason='Authorized100 Lean and12 Kani budgets exhausted; no further runs',target='not established',wallet_keys='No keys created, changed, deleted, or destroyed')
(ev/'RESUME5-FINAL-STATUS.json').write_text(json.dumps(finished,indent=2)+'\n')
all_timeout=all(int(x['exit'])==124 for x in verdicts)
summary='All12 native gates timed out; no verdict or checked shipped-source counterexample.' if all_timeout else 'Native outcomes differ; see exact per-gate exits/walls and logs; no row credit inferred.'
s=f'''# Resume5 final live status

Branch codex/pv-cb-20261026. Target not established. Budgets exhausted:
100/100 charged Lean attempts,80 pass/20 rejected;12/12 Kani complete.
Final reserved joint audits41300–41302 pass,65/108/19 declarations,
standard axioms only.81-entry focused source manifest checked;80 accepted
own objects retained. IDs41200–41302 consumed (three uncharged); next41303,
but no remaining budget. No capped scope remains active for this job.

{summary}
See RESUME5-KANI-TABLE.md and RESUME5-RECEIPTS-INDEX.json for bounds, timeouts,
wall, GNU RSS/swap, revision/input hashes and separate cgroup observations.
Timeout GNU RSS is wrapper rusage; final aggregate RSS is unavailable.
This is a focused audit, not a full privacy/deployment-closure release.

op223/V240 remains OPEN. No PV_CB_Op223Source.op223_source theorem was published.
Both transparent by-value shim configurations fail escaping-reference loan
validation; opaque wrapper success supplies no source equation. Actual legacy
and forest constructors have checked offset/row/bank invariants. All16 returned
words are canonical under selected-cell read validity. Tag/sampler invariants
and complete-Result sampled caller transport are proved, with native canonical16
agreement and full compiled-trace/auxiliary translation association still open.

V164 before/after source is byte-identical. P_source_p6, P_proof_bytes and
reservation unchanged;23/73 candidate rows; endpoint premise removals0.
All pre-existing own Lean sources, ProverRw, crates/programs and release pins
unchanged. The150.7s reservation-wait deviation is recorded; later drivers
check180s internally. No nonstandard axiom or source-row counterexample.

Own solver files and Rust cache cleanup receipts are retained separately;
source/evidence/pinned tools/accepted Lean objects remain. No wallet keys touched.
Next:close the exact op223 source proposition in RESUME5-OBLIGATIONS.md,
then let the read-only V164 consumer owner consume it. No privacy claim follows
from the present conditional helper proofs or timeout results.
'''
(ev/'RESUME5-LIVE-STATUS.md').write_text(s)
print('Final evidence prepared; exact native exits',verdicts)
