#!/usr/bin/env python3
"""Reconcile new ELF identities with retained ownership, without completeness."""
import argparse,collections,hashlib,importlib.util,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence';E=B/'s10-repin-20261022'
spec=importlib.util.spec_from_file_location('original_policy',R/'tools/s10-inventory-20261021/inventory.py')
policy=importlib.util.module_from_spec(spec);spec.loader.exec_module(policy)
def load(p):return json.loads(p.read_text())
def build():
 old=load(B/'s10-inventory-20261021/inventory.json')
 graphs=load(E/'elf-graphs.json')['artifacts'];raw=load(E/'elf-raw-input.json');rows=[]
 overlay=load(B/'lead-repin-20261022/ownership.json')
 for r in raw:
  mode=r['artifact'];name=r['name'];g=graphs[mode]
  previous=[p for p in old['declarations'] if p.get('artifact')==mode and p.get('name')==name and p.get('evidence')=='linked symbol']
  owners,boundary=policy.proposal(name)
  if previous:
   assert all(p['owners']==previous[0]['owners'] and p['trusted_boundary']==previous[0]['trusted_boundary'] for p in previous),name
   owners,boundary=previous[0]['owners'],previous[0]['trusted_boundary']
  if name=='entrypoint':owners,boundary=['Pool caller' if mode=='pool' else 'S2'],None
  rows.append(dict(**r,evidence='linked symbol',owners=owners,trusted_boundary=boundary,
   reachability='direct entrypoint lower bound' if r['address'] in g['direct_reachable'] else 'linked candidate; indirect reachability unresolved',
   ownership_basis='same resolved declaration policy; new address/ELF identity independently generated',
   source_instance_resolution='OPEN: final inline correspondence and concrete source Calls tree unavailable'))
 assert len({r['id'] for r in rows})==len(rows)
 unresolved=[r['id'] for r in rows if len(r['owners'])+int(r['trusted_boundary'] is not None)!=1]
 return dict(schema='s10-adopted-elf-inventory-v1',source_revision=load(E/'source-inputs.json')['source_revision'],
  declarations=rows,unassigned=unresolved,assigned_twice=[r['id'] for r in rows if len(r['owners'])>1],
  ownership_overlay=overlay,
  ownership_overlay_status='Retained source-level proposal only; historical closure/constant/span/compiler IDs are not adopted identities. New frozen MIR census and deltas are separate.',
  direct_reachability={m:dict(roots=g['roots'],direct_reachable=g['direct_reachable'],indirect_calls=g['indirect_calls']) for m,g in graphs.items()},
  complete=False,status='INCOMPLETE',
  residuals=['S2 caller identities','complete final instance/inline correspondence','owner acceptance','concrete source Calls tree/carriers','source/model ordered identities','coherent final release replay'],
  print_axioms='N/A: no Lean theorem added')
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');a.add_argument('--require-complete',action='store_true');args=a.parse_args()
 x=build();raw=(json.dumps(x,indent=2,sort_keys=True)+'\n').encode();p=E/'inventory.json'
 if args.check:assert p.read_bytes()==raw
 else:p.write_bytes(raw)
 print(json.dumps(dict(status=x['status'],records=len(x['declarations']),unassigned=len(x['unassigned']),assigned_twice=len(x['assigned_twice']),residuals=x['residuals'])))
 if args.require_complete:raise SystemExit(2)
