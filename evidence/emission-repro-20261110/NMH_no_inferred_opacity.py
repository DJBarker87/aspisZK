#!/usr/bin/env python3
"""Unrecovered diagnostic configurations use no guessed opaque boundaries."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=json.loads((E/'NMH_PLAN.json').read_text());changed=[]
for r in p['runs']:
 if not r.get('diagnostic_only'):continue
 assert not (E/r['run']/'receipt.json').exists()
 cc=r['charon_command'];new=[];i=0
 while i<len(cc):
  if cc[i]=='--opaque':i+=2;continue
  new.append(cc[i]);i+=1
 if new!=cc:changed.append(r['run'])
 r['charon_command']=new;r['configuration']['charon_command']=new;r['configuration']['opaque']=[];r['opacity']=[];r['basis']+=' No inferred opaque selectors: full reached frozen callee bodies are extracted. NHR opacity checks stay enabled; selected opaque list is genuinely empty.'
 (E/(r['run']+'_spec.json')).write_text(json.dumps(r,indent=2)+'\n')
p['diagnostic_opacity_policy']='No guessed opaque selectors; full reached native callee bodies, original NHR validation unchanged.';(E/'NMH_PLAN.json').write_text(json.dumps(p,indent=2)+'\n');print('removed inferred opaque cuts before launch:',','.join(changed))
