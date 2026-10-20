#!/usr/bin/env python3
"""Validate final focused receipts without rerunning unchanged Lean targets."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[5]
base=root/'docs/research/100bit-spend-path-20261013';ev=Path(__file__).resolve().parent
manifest=json.loads((ev/'manifest.json').read_text())
checks=[]
for src in sorted((base/'lean').glob('OracleDecisionFeasibility*.lean')):
 name=src.stem; sha=hashlib.sha256(src.read_bytes()).hexdigest()
 attempts=[r for r in manifest['attempts'] if r['module']==name and r['source_sha256']==sha and r['exit']==0]
 assert attempts, f'missing current green receipt: {name}'
 receipt=attempts[-1]; folder=ev/(name+'-'+str(receipt['attempt']))
 assert (folder/'source.lean').read_bytes()==src.read_bytes()
 declarations=re.findall(r'^theorem\s+(\w+)',src.read_text(),re.M)
 printed=re.findall(r'^#print axioms (\w+)',src.read_text(),re.M)
 assert sorted(declarations)==sorted(printed),(name,declarations,printed)
 assert len(receipt['axioms'])==len(printed)
 for report in receipt['axioms']:
  atoms=set(re.findall(r'\b(?:propext|Classical\.choice|Quot\.sound|sorryAx)\b',report))
  assert 'sorryAx' not in atoms
  body=report.split('depends on axioms: ',1)[-1]
  if body.startswith('['):
   axioms={x.strip() for x in body.strip('[]').split(',')}
   assert axioms <= {'propext','Classical.choice','Quot.sound'}, axioms
 assert not re.search(r'\b(?:sorry|admit|native_decide|maxHeartbeats|maxRecDepth)\b',src.read_text())
 for dep in receipt['direct_imports']:
  assert hashlib.sha256(Path(dep['path']).read_bytes()).hexdigest()==dep['sha256'],dep
 checks.append({'module':name,'attempt':receipt['attempt'],'exit':receipt['exit'],'source_sha256':sha,'receipt_revision':receipt['source_revision'],'wall_seconds':receipt['wall_seconds'],'peak_rss_bytes':receipt['peak_rss_bytes'],'swaps':receipt['swaps'],'theorems':len(printed)})
changed=subprocess.check_output(['git','diff','--name-only','7dac4fa12','--'],cwd=root,text=True).splitlines()
assert all('/lean/' not in p or Path(p).name.startswith('OracleDecision') for p in changed)
summary={'status':'pass','scope':'focused cache-based study evidence; not a frozen-manifest or clean unified release replay','base':'7dac4fa12','audited_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'targets':checks,'final_theorems':sum(x['theorems'] for x in checks),'compile_attempts':len(manifest['attempts']),'failed_attempts':sum(x['exit']!=0 for x in manifest['attempts']),'prelaunch_aborts':len(manifest.get('prelaunch_aborts',[])),'peak_rss_bytes':max(x['peak_rss_bytes'] for x in manifest['attempts']),'all_swaps':sum(x['swaps'] or 0 for x in manifest['attempts'])}
(ev/'audit.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
