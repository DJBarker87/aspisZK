#!/usr/bin/env python3
"""PCUC_ingest.py ROUND BK LOGFILE: ingest a bundle Lean log (state<ROUND-1> -> state<ROUND>) for every label of the bundle."""
import json,subprocess,sys
sys.path.insert(0,'.')
from PCUC_gen_all import cmd_for
rnd,bk,log=sys.argv[1:4];rnd=int(rnd);prev=rnd-1
prep=json.load(open('gen_prepared.json'));ms=json.load(open('gen/bundles.json'))[bk]
def info(label):
    for key,r in prep.items():
        for ps in r.get('passes',[]):
            if r['module'].replace('.','_')+ps['tag']==label: return key,r,ps
for label in ms:
    key,r,ps=info(label)
    p=subprocess.run(cmd_for(key,r,ps,label,rnd,prev,log,bk),capture_output=True,text=True)
    print(label,p.returncode,p.stdout.strip()[-150:],p.stderr.strip()[-300:])
