#!/usr/bin/env python3
"""Validate completed receipts and source boundaries; never promote diagnostics."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/ckpt-abi2-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((E/'manifest.json').read_text());current=[a for a in manifest['attempts'] if a.get('final_current')]
for a in current:
 assert a['exit']==0 and a['swaps']==0
 source=B/'lean'/(a['module'].replace('.','/')+'.lean');assert sha(source)==a['source_sha256'],source
 for line in a['axioms']:
  if 'depends on axioms:' in line:
   names=re.search(r'\[([\s\S]*?)\]',line)[1].replace('\n','').split(',')
   assert all(n.strip() in ['propext','Classical.choice','Quot.sound'] for n in names),line
final=[]
for name in ['final-decode-k','final-decode-e','final-encode-k','final-encode-e-byte','final-writer']:
 p=E/'host/receipts'/name;d=json.loads((p/'receipt.json').read_text())
 assert d['exit_status']==0 and d['swaps']==0
 assert 'VERIFICATION SUCCESSFUL' in (p/'stdout.log').read_text()
 assert d['source_sha256']['tools/oracle-port-ckpt-abi2/src/lib.rs']==sha(R/'tools/oracle-port-ckpt-abi2/src/lib.rs')
 assert d['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert '--unwinding-assertions' in d['target'];final.append(d)
changed=subprocess.check_output(['git','diff','--name-only','ec56a3486','--','crates','programs'],cwd=R,text=True).splitlines();assert not changed
new_lean=sorted((B/'lean').glob('OraclePortCkptAbi2*.lean'))+sorted((B/'lean/OraclePortCkptAbi2Extracted').glob('*.lean'))
for p in new_lean:
 s=p.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|^set_option max(?:Heartbeats|RecDepth)',s,re.M),p
# This checks a local packet, not a coherent frozen release or a cone endpoint.
result=dict(schema='checkpoint-abi2-focused-audit-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),current_lean_targets=[a['module'] for a in current],theorems=sum(len(re.findall(r'^theorem ',p.read_text(),re.M)) for p in new_lean),final_kani_targets=[a['attempt'] for a in final],shipped_changes=changed,elf_rebuild_required=False,standard_axioms_only=True,complete_checkpoint_cone=False,accepted_run_join=False,whole_reader_certified=False,full_frozen_manifest_replayed=False)
(E/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
