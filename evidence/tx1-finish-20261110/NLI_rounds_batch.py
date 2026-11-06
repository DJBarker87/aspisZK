from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
plan=[(6,'rounds_running_cut',True),(7,'rounds_running_control',False),(8,'rounds_alpha_cut',True),(9,'rounds_alpha_control',False),(10,'rounds_transcript_cut',True),(11,'rounds_transcript_control',False),(12,'rounds_input_stability_cut',True),(13,'rounds_input_stability_control',False)]
for n,name,positive in plan:
 a=f'NLI_K{n:03d}'
 subprocess.run([sys.executable,str(E/'NLI_kconfig.py'),a,'NLI_program::'+name],check=True)
 r=subprocess.run([sys.executable,str(E/'NLI_run.py'),a])
 p=E/a/'stdout.log'
 if not p.exists():sys.exit(1)
 s=p.read_text();receipt=json.loads((E/a/'receipt.json').read_text())
 expected=(r.returncode==0 and 'VERIFICATION:- SUCCESSFUL' in s) if positive else (r.returncode!=0 and 'Failed Checks: assertion failed: !selected' in s and 'timed out' not in s.lower())
 (E/(a+'-verdict.json')).write_text(json.dumps(dict(attempt=a,expected='PASS' if positive else 'MATCHED_ASSERTION_FAIL',accepted=expected,exit=receipt['exit_status'])))
 if not expected:sys.exit(1)
