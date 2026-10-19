#!/usr/bin/env python3
"""Validate the decode-reuse caller proof and its coherent reference cache."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4]
evidence=area/'evidence/cu-equivalence-20261019'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
source_check=json.loads(subprocess.check_output([sys.executable,str(here/'check-public-decode-source.py'),'--check'],text=True))
assert source_check['source_delta_checked'] and source_check['exit_status']==0
attempts={
 'CuSavingsPublicDecode':'cu-public-decode-a',
 'CuSavingsPublicDecodeSource':'cu-public-decode-source-e',
 'CuSavingsPublicDecodeTransfer':'cu-public-decode-transfer-b',
 'CuSavingsPublicDecodePreparation':'cu-public-decode-preparation-b'}
owners={
 'AspisR1PublicPreparation.Types':'e1d3e2db77e3e3730db804bb1a32d75546a18b4929a4e38a3017afd489450922',
 'AspisR1PublicPreparation.Funs':'063480804f71daba2bf1775526611da2bbe0d3e943ba865f571fc91039420359',
 'Aeneas':'d3bfce818c2409992274bc1852aa00280cb7a8139465ef0bab674498e4cdc69d'}
records={}
for module,attempt in attempts.items():
 directory=evidence/attempt;receipt=read(directory/'receipt.json')
 assert receipt['source_sha256']==sha(area/'lean'/(module+'.lean'))==sha(directory/'source.lean'),module
 assert receipt['exit_status']==0 and receipt['process_swaps']==0 and receipt['cgroup_swap_bytes']==0,module
 assert receipt['cgroup_limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
 assert sum(value for _,value in receipt['reservations'])<=50*2**30,module
 log=receipt['print_axioms_output'];assert 'sorryAx' not in log and 'error:' not in log
 axioms={name.strip() for block in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log) for name in block.split(',')}
 assert axioms<={'propext','Classical.choice','Quot.sound'},(module,axioms)
 if module!='CuSavingsPublicDecode':
  provenance=receipt['cache_provenance'];cached=read(directory/'cache-receipt.json')
  assert provenance['sha256']==sha(directory/'cache-receipt.json')
  assert provenance['priority']=='NEW_CU_MODULES_THEN_EXACT_ORIGINAL_CLOSURE'
  assert cached['exit_status']==0 and cached['axioms']['passed']
  assert cached['target']=='ExtractedFirstHelperBinding'
  actual_source=receipt['cache_target_source']
  assert sha(repo/actual_source['path'])==actual_source['sha256']==cached['source_manifest_entry']['source_sha256']
  for name,expected in owners.items():assert provenance['selected_owner_objects'][name]['sha256']==expected,(module,name)
  for name,pin in provenance['selected_cache_objects'].items():
   expected=cached['objects']['.olean'] if name==cached['target'] else cached['key']['imports'][name]['objects']['.olean']
   assert pin['sha256']==expected['sha256'],(module,name)
 records[module]=dict(attempt=attempt,receipt_sha256=sha(directory/'receipt.json'),source_sha256=receipt['source_sha256'])
# Retain the observed nominal-module shadow as a superseded environment, not
# release evidence. Rechecking affected targets was justified by this change.
mixed=read(evidence/'cu-public-decode-preparation-a/receipt.json')
assert mixed['exit_status']!=0 and 'Unknown constant `AspisR1PublicPreparation.verifier.Error`' in mixed['print_axioms_output']
assert 'aspis-joint-20261019/objects' in mixed['lean_path']
print(json.dumps(dict(status='CHECKED_CALLER_AND_PREPARATION_TRANSFER',targets=records,
 reference_owner_objects=owners,source_check=source_check,
 superseded_mixed_cache_attempts=['cu-public-decode-source-b','cu-public-decode-source-c','cu-public-decode-source-d','cu-public-decode-transfer-a','cu-public-decode-preparation-a'],
 scope='Candidate 6 caller equivalence and consuming original helper/serializer theorem under its unchanged downstream/source-model boundaries. This is not the final optimized-verifier security transfer.',full_goal_complete=False)))
