#!/usr/bin/env python3
"""Collect every focused attempt, including excluded failed elaborations."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/child-joins-20261023'
p=E/'manifest.json';x=json.loads(p.read_text());x['attempts']=[]
for f in sorted(E.glob('lean-*/receipt.json')):
 r=json.loads(f.read_text());x['attempts'].append(dict(receipt=str(f.relative_to(R)),attempt=r['attempt'],target=r['sources'],source_revision=r['source_revision'],source_hashes=r['source_hashes'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],print_axioms=r['print_axioms'],accepted=r['exit_status']==0,receipt_sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
x['budget']={'prior_lean_used':4,'fresh_lean_used':len(x['attempts'])-4,'fresh_lean_limit':100,'fresh_kani_used':0,'fresh_kani_limit':40}
x['status']='Fixed C5 decoder and accepted_run proved; concrete checkpoint endpoint authentication proved; native op10/op11 installation open; later stages deferred by depth-first order'
x['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
p.write_text(json.dumps(x,indent=2)+'\n')
