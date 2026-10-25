#!/usr/bin/env python3
from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent; H='/home/dombarker/project-offloads/codex-cx-lowering2-20261026'; remote='dombarker@100.108.41.90'
files={'Low2_build_manifest.json':'Low2_build_manifest.json'}
for b in ['build-default-v1','build-default-v2','build-devnet-v1','build-pool-v1']:
 for f in ['receipt/receipt.json','receipt/time.log','receipt/stdout.log','receipt/stderr.log','command.json','reservation.json']:
  files[b+'/'+f]='Low2_'+b+'_'+f.replace('/','_')
 if b!='build-default-v1':files[b+'/artifact-comparison.json']='Low2_'+b+'_artifact.json'
for src,dst in files.items():subprocess.run(['scp','-q',remote+':'+H+'/'+src,str(E/dst)],check=True)
