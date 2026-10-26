from pathlib import Path
import json,hashlib,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(P.glob('P2P_*/receipt.json'))]
assert len(receipts)==100,len(receipts)
assert [r['attempt'] for r in receipts]==[f'P2P_{n:03}' for n in range(1,101)]
success=[r for r in receipts if r['exit_status']==0];fail=[r for r in receipts if r['exit_status']]
assert all(r['swaps']=='0' for r in receipts)
assert all('-M7000' in r['command'] for r in receipts)
for r in receipts:
 assert r['limits']==receipts[0]['limits'],r['attempt']
 assert int(r['peak_rss_kib'])<8*1024*1024,r['attempt']
 assert r['exit_status'] in [0,1],r['attempt']
 for line in r['print_axioms'] if r['exit_status']==0 else []:
  assert all(a.strip() in ['propext','Classical.choice','Quot.sound'] for a in re.search(r'\[(.*?)\]',line)[1].split(',')) if '[' in line else 'does not depend on any axioms' in line,line
snapshots={}
for r in success:
 for file,h in r['source_hashes'].items():snapshots.setdefault(file,[]).append((r['attempt'],h))
modules=[];theorems=[]
axioms='\n'.join(line for r in success for line in r['print_axioms'])
for file in sorted((R/'lean').glob('P2P_*.lean')):
 s=file.read_text();matches=[a for a,h in snapshots.get(file.name,[]) if h==sha(file)]
 assert matches,('no passing exact source',file.name)
 assert not re.search(r'(?m)^\s*(?:axiom\s|.*\b(?:sorry|admit|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats))',s),file
 modules.append(dict(module=file.stem,source_sha256=sha(file),passing_attempts=matches))
 if file.stem.startswith('P2P_Audit'):continue
 ns=re.search(r'^namespace (\S+)',s,re.M)
 for t in re.findall(r'(?m)^theorem (\w+)',s):
  name=ns[1]+'.'+t
  assert name in axioms,('no passing printed audit',name)
  theorems.append(name)
changed=subprocess.check_output(['git','diff','--name-only','aa1f898c59'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/P2P_') or p.startswith('evidence/p2prime-20261026/') for p in changed),changed
assert not any(p.endswith(('.olean','.elf','.tar','.gz')) for p in changed)
manifest=[]
for r in receipts:
 rr=dict(r);rr['receipt_path']=str((P/r['attempt']/'receipt.json').relative_to(R));manifest.append(rr)
(P/'P2P_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in manifest))
result=dict(lean_attempts=len(receipts),passing=len(success),excluded_failures=[r['attempt'] for r in fail],kani_runs=0,wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,limits=receipts[0]['limits'],current_modules=modules,new_theorems=theorems,all_current_sources_match_successful_receipts=True,standard_axioms_only=True,source_scope_check=True,full_manifest_replay=False,release_claim=False)
(P/'P2P_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['current_modules','new_theorems']},indent=2))
