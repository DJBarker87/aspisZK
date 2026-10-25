#!/usr/bin/env python3
"""Sequential focused proof repins, stop at first failure; shared local lock."""
from pathlib import Path
import subprocess,json
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';T=Path(__file__).parent;j=json.loads((T/'support-binding.json').read_text());paths=Path('/tmp/s126-s6-sdk-first-path-20261024.txt').read_text().strip();out=E/'s1-mask-support-driver-v1';out.mkdir(exist_ok=False);rows=[]
for k,row in enumerate(j['targets']):
 attempt=f's1-mask-support-{k+1:02}-v1';cmd=['python3',str(R/'tools/s126-sdk-20261021/lean-local.py'),row['module'],attempt,paths,str((B/'lean-candidates/s1-mask-support-20261025').relative_to(R))]
 p=subprocess.run(cmd,cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(out/(attempt+'.log')).write_text(p.stdout);rec=json.loads((E/attempt/'receipt.json').read_text())if (E/attempt/'receipt.json').exists()else{};rows.append(dict(target=row['module'],attempt=attempt,driver_exit=p.returncode,exit_status=rec.get('exit_status'),wall_seconds=rec.get('wall_seconds'),peak_rss_bytes=rec.get('peak_rss_bytes'),swaps=rec.get('swaps')));(out/'results.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows[-1]),flush=True)
 if p.returncode!=0:raise SystemExit(p.returncode)
