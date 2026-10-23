from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2g-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=json.loads((E/'object-base.json').read_text());rows=[]
for p in sorted(E.glob('*/receipt.json')):
 x=json.loads(p.read_text());assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},p
 assert x['swaps']=='0',p
 for f,h in x['source_hashes'].items():assert sha(p.parent/'sources'/f)==h,(p,f)
 if x['kind']=='lean':
  delta=json.loads((p.parent/'objects-delta.json').read_text());values=dict(base);values.update(delta['changed'])
  for k in delta['removed']:values.pop(k)
  digest=hashlib.sha256((json.dumps(values,sort_keys=True,indent=2)+'\n').encode()).hexdigest()
  assert digest==delta['original_sha256']==x['deps_fingerprint']['selected_overlay_sha256'],p
  if x['exit_status']==0:
   assert x['print_axioms'],p
   for line in x['print_axioms']:
    assert 'sorryAx' not in line,p
    if 'depends on axioms:' in line:assert set(re.findall(r'\[([^]]*)\]',line)[0].split(', ')) <= {'propext','Classical.choice','Quot.sound'},(p,line)
 if x['kind']=='kani':
  s=(p.parent/'stdout.log').read_text();assert x['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s,p
  checks=re.findall(r'\*\* (\d+) of (\d+) failed',s);assert checks and all(n=='0' for n,_ in checks)
  assert 'profile [optimized]' in s,p
 rows.append({'receipt':str(p.relative_to(E)),**{k:x[k] for k in ['attempt','kind','source_revision','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','deps_fingerprint']},'status':'accepted scoped local result' if x['exit_status']==0 else 'excluded failure; recovery axioms earn no proof credit'})
final=json.loads((E/'lean-012/receipt.json').read_text());assert final['exit_status']==0
for p in (D/'lean').glob('S2G_*.lean'):
 assert final['source_hashes'][p.name]==sha(p),p
 s=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)',s,re.M),p
 for theorem in re.findall(r'^theorem (\w+)',s,re.M):assert '#print axioms '+theorem in s,p
assert len(final['print_axioms'])==14
k1=(E/'kani-001/sources/S2G-contracts/src/lib.rs').read_text();k2=(E/'kani-002/sources/S2G-contracts/src/lib.rs').read_text();assert k1.split('#[kani::proof_for_contract')[0]==k2.split('#[kani::proof_for_contract')[0]
assert k2==(E/'S2G-contracts/src/lib.rs').read_text()
assert '2 of 2 cover properties satisfied' in (E/'kani-001/stdout.log').read_text()
catalog=json.loads((E/'contracts.json').read_text());assert len(catalog['all_children'])==13
expected={'decode','validate','candidate','first','copy','drop_checkpoint','drop_statement','validate_asq8','public','second','emit','clear_return_data','SolanaDigest'}
assert {r['child'] for r in catalog['all_children']}==expected
for x in catalog['all_children']:assert x['missing_theorem'] and not x['native_children_field_closed']
for x in catalog['sources'].values():assert sha(D/x['path'])==x['sha256']
start=json.loads((E/'stage0.json').read_text())['source_revision']
assert not subprocess.check_output(['git','diff',start,'--','crates','programs','Cargo.lock','Cargo.toml','.cargo'],cwd=R,text=True)
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.so','.elf','.tar','.gz'} and p.stat().st_size<=5*1024**2,p
counts={'lean':len(list(E.glob('lean-*.json')))//2,'kani':len([r for r in rows if r['kind']=='kani'])}
# Each Lean slot has a command and reservation file, including the excluded
# pre-launch setup failure. Count conservatively, not as successful compiles.
assert counts=={'lean':12,'kani':2},counts
assert counts['lean']<=100 and counts['kani']<=60
manifest={'schema':'focused-extractor-proof-packet-v1','status':'PARTIAL; no concrete native Children instance; S2 target not yet established','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'budget_used_conservatively':counts,'actual_lean_invocations':11,'limits':{'lean':100,'kani':60},'new_native_Required14_fields':[],'shipped_changes':False,'new_trust':False,'final_focused_axioms_audit':'lean-012/receipt.json','contract_catalog':'contracts.json','copy_contract_and_consumer':['kani-001/receipt.json','kani-002/receipt.json'],'excluded_setup_failure':'lean-005/setup-failure.json','object_inventory_format':'object-base.json + each objects-delta.json reconstruct exact selected_overlay_sha256; focused cached evidence, no coherent release replay','attempts':rows}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':manifest['status'],'budget':counts,'audits':14,'shipped_changes':False,'source_snapshots':'matched','object_fingerprints':'reconstructed and matched'}))
