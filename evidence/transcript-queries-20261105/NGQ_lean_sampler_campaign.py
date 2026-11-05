from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
for number,target in [(24,'NGQ_SamplerTrace'),(25,'NGQ_SamplerConstruct'),(26,'NGQ_SamplerDriver'),(27,'NGQ_SamplerNative')]:
 a=f'NGQ_L{number:03}'
 r=subprocess.run(['python3',str(E/'NGQ_run.py'),a,'lean',target],text=True,capture_output=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit(a+' missing receipt; recover before proceeding')
 rc=json.loads(p.read_text());print(a,target,rc['exit_status'],rc['wall_seconds'],rc['peak_rss_kib'],flush=True)
 if r.returncode:raise SystemExit(r.returncode)
