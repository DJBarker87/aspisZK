from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
rows=json.loads((E/'NBS_COPY_RECHECK_PLAN.json').read_text())['rechecks']
# K025 was codegen-only; K026 repaired the generic Vec denial stub. Rechecks
# start at K027 and stop at K039, retaining one native slot until Lean finishes.
for attempt,row in zip(range(27,40),rows[1:14]):
 a=f'NBS_K{attempt:03}'
 r=subprocess.run(['python3',str(E/'NBS_kani.py'),a,row['crate'],row['harness'],str(E/'NBS_copy_hooks.patch')],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json';assert p.exists(),r.stdout+r.stderr
 x=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 print(a,row['original_harness'],x['exit_status'],x['wall_seconds'],flush=True)
 if 'timed out' in log or x['exit_status'] in [124,137]:
  c=subprocess.run(['python3',str(E/'NBS_cleanup_solver.py'),a],capture_output=True,text=True);assert c.returncode==0,c.stderr
 # These are independent source functions; a failed gate receives no credit
 # and is not repeated. Do not continue after codegen/infrastructure failures.
 if x['exit_status'] and not ('VERIFICATION:-' in log):raise SystemExit(r.stdout[-3500:]+r.stderr)
