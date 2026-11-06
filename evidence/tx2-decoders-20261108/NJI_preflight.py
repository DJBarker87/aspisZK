from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
out=E/'NJI_PREFLIGHT';out.mkdir(exist_ok=True)
r=subprocess.run(['python3','NHR_stage.py','--check','--out','NJI_PREFLIGHT'],capture_output=True,text=True)
(out/'validation.stdout').write_text(r.stdout);(out/'validation.stderr').write_text(r.stderr)
h=subprocess.run(['/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon','--help'],capture_output=True,text=True)
(out/'charon-help.txt').write_text(h.stdout+h.stderr)
print(json.dumps(dict(validation_exit=r.returncode,help_exit=h.returncode)))
raise SystemExit(r.returncode)
