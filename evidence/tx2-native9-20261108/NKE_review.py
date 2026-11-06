"""Final read-only release gates except temporary patch reconstruction."""
from pathlib import Path
import json,hashlib,sys,tempfile,subprocess
B=Path.cwd();mode=sys.argv[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if mode=='native':
 rows=[json.loads(p.read_text()) for p in sorted(B.glob('NKE_K*/receipt.json'))];assert len(rows)==40
 for r in rows:
  a=r['attempt'];g=json.loads((B/(a+'-graph-check.json')).read_text());lock=json.loads((B/(a+'-lock-check.json')).read_text());source=json.loads((B/(a+'-source-check.json')).read_text())
  assert g['graph_matches_frozen'] and lock['unchanged'] and not source['errors'],a
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and r['swaps']=='0',a
  cmd=r['native_command'];assert cmd[cmd.index('--features')+1]=='private-leaf-salts,optimized-terminal,program-build'
  assert r['env']['CARGO_TARGET_DIR']==str(B/'NKE_target')
 pairs=json.loads((B/'NKE_NATIVE_PAIRS.json').read_text())['pairs'];assert len(pairs)==13
 for pair in pairs:
  a,b=[json.loads((B/pair[k]/'receipt.json').read_text()) for k in ['positive','control']]
  assert a['exit_status']==0 and b['exit_status']==1 and a['source_hashes']==b['source_hashes']
 r=dict(status='PASS',native_scopes=40,matched_pairs=13,frozen_offline_graphs=40,unchanged_locks=40,source_checks=40,optimized=True,swap=0,row_credit=False)
elif mode=='patch':
 suffix='\n#[cfg(kani)]\n#[path = "NKE_parent.rs"]\nmod NKE_parent;\n'
 with tempfile.TemporaryDirectory(prefix='NKE_patch_',dir=B/'NKE_tmp') as tmp:
  root=Path(tmp)
  for n in ['candidate.rs','lib.rs']:
   rel=Path('crates/aspis-r1-cost-probe/src')/n;s=(B/'NKE_src'/rel).read_text()
   if n=='candidate.rs':assert s.endswith(suffix);s=s[:-len(suffix)]
   else:s=s.replace('#![cfg_attr(kani,feature(allocator_api))]\n','')
   q=root/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s)
  process=subprocess.run(['patch','-p1','--batch','--forward','-i',str(B/'NKE_HARNESS.patch')],cwd=root,capture_output=True,text=True);assert process.returncode==0,process.stdout+process.stderr
  checked=[]
  for q in root.rglob('*'):
   if q.is_file():
    rel=q.relative_to(root);assert q.read_bytes()==(B/'NKE_src'/rel).read_bytes(),str(rel);checked.append(str(rel))
 r=dict(status='PASS',patch_sha256=sha(B/'NKE_HARNESS.patch'),scratch_roundtrip_files=checked,shipped_files_modified=False)
elif mode=='inventory':
 occurrences=json.loads((B/'NKE_OCCURRENCES.json').read_text());names={x['occurrence'] for x in occurrences}
 assert {f'R{i:02}' for i in range(1,46)}<=names and {f'C{i:02}' for i in range(1,10)}<=names
 closed=json.loads((B/'NKE_CLOSED.json').read_text());delta=json.loads((B/'NKE_LEDGER_DELTA.json').read_text());assert not closed['functions'] and not closed['security_target_established'] and not delta['transitions']
 assert delta['counts_before']==delta['counts_after']=={'CLOSED':514,'OPEN':85}
 roots=json.loads((B/'NKE_AUDIT_ROOTS.json').read_text())['roots'];results=[]
 for p in (B/'NKE_audit').glob('batch*/proof*.json'):
  row=json.loads(p.read_text());assert row['exit_status']==0;results+=row['results']
 assert len(results)==len(roots) and {x['root'] for x in results}==set(roots)
 assert all(x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in results)
 assert json.loads((B/'NKE_audit/scan/scan.json').read_text())['exit_status']==0
 r=dict(status='PASS',occurrences=len(occurrences),raw_roots=len(roots),source_ordered=True,new_closed_rows=0,TX2_065='OPEN',security_target_established=False)
else:raise ValueError(mode)
(B/('NKE_REVIEW_'+mode+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
