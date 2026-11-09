#!/usr/bin/env python3
"""PCT_controls.py: self-copy controls. For each module with an unproved reached definition (or uncovered), each (<=3) single-namespace gate candidate text
becomes the 'fresh' directory (renamed namespace) and is compared with the gate constants. A candidate whose common declarations are all rfl/unfold is the compiled source."""
import json,subprocess,sys,re
from pathlib import Path
sys.dont_write_bytecode=True
sys.path.insert(0,'.')
import PCT_gen_equalities as G
def show(p):
    r=subprocess.run(['git','show',f'research:{p}'],capture_output=True)
    return r.stdout.decode('utf-8','replace') if r.returncode==0 else None
prep=json.load(open('gen/prepared2.json'));st=json.load(open('PCT_STATUS.json'))['modules'];P=json.load(open('PCT_PARTITION.json'))['modules']
ctl={}
for m,v in st.items():
    if all(x['status'] in('PROVED_RFL','PROVED_UNFOLD') for x in v['reached'].values()): continue
    kind=prep[m]['kind'];k=0
    for cand in P[m]['candidates']:
        t=show(cand['paths'][0])
        if t is None: continue
        ns=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(t))
        if len(ns)!=1: continue
        k+=1
        if k>3: break
        label=m.replace('.','_')+f'_ctl{k}';d=Path('inputs/fresh_'+label);d.mkdir(exist_ok=True)
        (d/'Funs.lean').write_text(t);(d/'Types.lean').write_text(t)
        Path('inputs/gate_'+label+'.lean').write_text(t)
        cmd=['python3','-B','PCT_gen_equalities.py','--partition','PCT_PARTITION.json','--module',m,'--tag',f'_ctl{k}','--fresh-dir',str(d),'--fresh-ns',ns[0],'--gate-source','inputs/gate_'+label+'.lean',
             '--out',f'PRVEq_{label}.lean','--report',f'gen/PRVEq_{label}.report1.json','--state-out',f'gen/PRVEq_{label}.state1.json']
        if kind!='Types': cmd+=['--gate-types-source','inputs/gate_'+label+'.lean']
        p=subprocess.run(cmd,capture_output=True,text=True)
        ctl[label]=dict(module=m,candidate_sha=cand['sha256'],path=cand['paths'][0],rc=p.returncode,err=p.stderr.strip()[-150:])
        print(label,p.returncode,p.stderr.strip()[-100:])
Path('gen/controls.json').write_text(json.dumps(ctl,indent=1))
