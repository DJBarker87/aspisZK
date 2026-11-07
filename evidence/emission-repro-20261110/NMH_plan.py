#!/usr/bin/env python3
"""Group provenance inputs and recover exact archived command configurations."""
from pathlib import Path
import json,subprocess,hashlib,collections,re
E=Path(__file__).resolve().parent
INV=json.loads((E/'NMH_INVENTORY.json').read_text());REV=INV['revision']
def read(p):return subprocess.check_output(['git','show',REV+':'+p])
def commands(o):
 if isinstance(o,dict):
  if isinstance(o.get('charon_command'),list) and isinstance(o.get('aeneas_command'),list):yield o
  for v in o.values():yield from commands(v)
 elif isinstance(o,list):
  for v in o:yield from commands(v)
def vals(a,k):return [a[i+1] for i,v in enumerate(a[:-1]) if v==k]
def main():
 paths=sorted({p for z in INV['blobs'] for p in z['pin_receipt_paths']});records=[]
 for p in paths:
  try:raw=read(p);d=json.loads(raw)
  except (ValueError,subprocess.CalledProcessError):continue
  for c in commands(d):
   cc=c['charon_command'];ac=c['aeneas_command'];man=vals(cc,'--manifest-path');rel=None
   if man:
    m=re.search(r'((?:crates|programs)/[^/]+/Cargo.toml)$',man[0]);rel=m[1] if m else None
   records.append(dict(receipt=p,receipt_sha256=hashlib.sha256(raw).hexdigest(),charon_command=cc,aeneas_command=ac,roots=vals(cc,'--start-from'),features=vals(cc,'--features'),opaque=vals(cc,'--opaque'),include=vals(cc,'--include'),manifest=rel,namespace=vals(ac,'-namespace'),opacity=c.get('opacity',[])))
 # Keep exact command shapes distinct. No guessed metadata is upgraded to exact.
 groups={};members=[]
 for z in INV['blobs']:
  candidates=[c for c in records if c['receipt'] in z['pin_receipt_paths']]
  # Use namespace to distinguish multiple command sets in same metadata.
  exact=[c for c in candidates if any(n in z['namespace'] for n in c['namespace'])]
  candidates=exact or candidates
  key=json.dumps([z['crate_header'],z['namespace'],sorted(set(z['pin_receipt_paths']))],sort_keys=True)
  if key not in groups:
   groups[key]=dict(group='',crate=z['crate_header'],namespace=z['namespace'],configuration_candidates=candidates,configuration_basis='Archived command arrays from listed packet receipts; namespace match preferred. No proximity-only pin claim.' if candidates else 'Source annotations and namespace only; full crate/features/opaque/root configuration not recovered.',members=[],bytes=0)
  g=groups[key];g['members'].append(z['blob']);g['bytes']+=z['bytes']
 groups=sorted(groups.values(),key=lambda g:(g['bytes'],str(g['namespace'])))
 for i,g in enumerate(groups,1):g['group']='NMH_G%03d'%i
 out=dict(schema=1,inventory_revision=REV,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',pool_revision='b936275465',budgets=dict(Charon=30,Aeneas=30,Lean=10,Kani=0),ordering='smallest aggregate committed byte size first; executable configurations before unresolved groups; dependencies serial',groups=groups)
 (E/'NMH_PLAN.json').write_text(json.dumps(out,indent=2)+'\n');(E/'NMH_COMMAND_RECOVERY.json').write_text(json.dumps(records,indent=2)+'\n')
 print(json.dumps(dict(groups=len(groups),blobs=sum(len(g['members']) for g in groups),recovered_commands=len(records),groups_with_commands=sum(bool(g['configuration_candidates']) for g in groups))))
 for g in groups:
  if g['configuration_candidates']:print(g['group'],g['bytes'],g['namespace'],[(c['manifest'],c['roots']) for c in g['configuration_candidates'][:2]])
if __name__=='__main__':main()
