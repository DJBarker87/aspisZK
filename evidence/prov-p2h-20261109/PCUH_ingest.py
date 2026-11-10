#!/usr/bin/env python3
"""PCUH_ingest.py LABEL ROUND STATEFILE LOG OFFSETS: ingest one bundle log for one label; writes PRVEq_<LABEL>.lean (final text) and gen/PRVEq_<LABEL>.report<ROUND>.json."""
import sys,subprocess,json,collections,importlib.util
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('g',H/'PCUH_gen.py');g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
by={g.label(m,ps):(m,r,ps) for m,r,ps in g.passes()}
lab,rnd,st,log,offs=sys.argv[1:6]
m,r,ps=by[lab]
c=g.cmd(m,r,ps,f'PRVEq_{lab}.lean',f'gen/PRVEq_{lab}.report{rnd}.json',state_out=f'gen/PRVEq_{lab}.state{rnd}.json',state=st,log=log,offs=offs)
p=subprocess.run(c,capture_output=True,text=True);print(lab,p.returncode,p.stdout[-200:],p.stderr[-300:])
rep=json.load(open(H/f'gen/PRVEq_{lab}.report{rnd}.json'))
print(dict(collections.Counter(q['status'] for q in rep['per_definition'].values())))
for n,q in rep['per_definition'].items():
    if q['status'] not in('proved','given'): print('  ',n[:100],'|',q.get('error','')[:80])
