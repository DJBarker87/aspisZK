#!/usr/bin/env python3
"""Read/hash-only check of two rejected helper-only compiler attempts."""
from pathlib import Path
import hashlib,json,tarfile
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';E=BASE/'evidence/c2-helper-root-diagnostics-20261017'
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 arc=E/'helper-root-diagnostics.tar.gz';assert sha(arc.read_bytes())=='9b64fe50df2f41656258a777ce5144a91a2c8858755587f6cc82fbc3b63b93b0'
 members=json.loads((E/'helper-root-members.json').read_text())
 with tarfile.open(arc) as tf:files={m.name:tf.extractfile(m).read() for m in tf.getmembers() if m.isfile()}
 assert set(files)==set(members)
 for n,b in files.items():assert sha(b)==members[n]['sha256'] and len(b)==members[n]['bytes'],n
 for prefix,target,error in [('copy-helper-only','crate::prover::copy_c2_columns','symbolic/SymbolicToPureAbs.ml'),('retained-helper-only','crate::host_commitment::encode_and_retain_lanes','interp/InterpAbs.ml')]:
  pins=json.loads(files[prefix+'/input/source-pins.json']);assert pins['root_target']==target
  assert pins['classification'].startswith('UNADOPTED_DIAGNOSTIC')
  for n,h in pins['kit_files'].items():assert sha(files[prefix+'/input/'+n])==h
  assert not json.loads(files[prefix+'/C2OwnedHost.llbc'])['has_errors']
  for phase,exit in [('charon',0),('aeneas',2)]:
   key=prefix+'/runs/'+phase+'-a';r=json.loads(files[key+'/receipt.json'])
   assert r['phase']==phase and r['exit_status']==exit and r['root_target']==target
   assert r['source_revision']=='deb68369ba3ad7cc6706dc24b6503fac1cbe942b'
   assert r['source_pins_sha256']==sha(files[prefix+'/input/source-pins.json'])
   assert r['runner_sha256']==sha(files[prefix+'/run-host.py'])
   assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
   assert r['process_swaps']==0 and r['cgroup_swap_current']==0
   assert r['reservation']['total_memory_max_bytes']<r['reservation']['safe_limit_bytes']
   for n,h in r['outputs'].items():assert sha(files[prefix+'/'+n])==h
  assert error in files[prefix+'/runs/aeneas-a/stdout.log'].decode()
 print(json.dumps({'status':'PASS','archive_sha256':sha(arc.read_bytes()),'members':len(files),'rejected_helper_cones':2,'accepted_helper_cones':0,'new_proof_results':0,'production_changes':0},sort_keys=True))
if __name__=='__main__':main()
