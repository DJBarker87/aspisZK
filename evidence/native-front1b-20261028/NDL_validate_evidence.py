"""Local receipt/archive validation; does not rerun any prover."""
from pathlib import Path
import json,lzma,hashlib,collections,subprocess
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(s) for s in (E/'NDL_ATTEMPTS.jsonl').read_text().splitlines()];counts=collections.Counter(r['kind'] for r in rows)
assert dict(counts)==dict(kani=80,lean=80,extract=20);assert len({r['attempt'] for r in rows})==180
raw=lzma.decompress((E/'NDL_SOURCE_ARCHIVE.json.xz').read_bytes());assert sha(raw)==(E/'NDL_SOURCE_ARCHIVE.json.sha256').read_text().split()[0];archive=json.loads(raw);sources=archive['source_files'];pins=archive['historical_source_pinsets']
patches={}
for n,v in sources.items():
 if v['patch'] not in patches:
  lines=(E/v['patch']).read_text().splitlines(True)
  text=''.join(l[1:] for l in lines if l.startswith('+') and not l.startswith('+++ '));patches[v['patch']]=text
 assert sha(patches[v['patch']].encode())==v['sha256'],n
rust_checks=0;graphs=[]
for row in rows:
 a=row['attempt'];receipt=json.loads((E/a/'receipt.json').read_text());assert sha((E/a/'receipt.json').read_bytes())==row['receipt_sha256'];assert row['exit_status']==receipt['exit_status']
 for key,value in [('memory.high','6442450944'),('memory.max','8589934592'),('memory.swap.max','0'),('pids.max','64')]:assert str(receipt['limits'][key])==value,(a,key)
 assert str(receipt['swaps'])=='0'
 admission=json.loads((E/(a+'-admission.json')).read_text());assert admission['exit']==0 and admission['reservation']['allowed'] is True
 for n,h in receipt['source_hashes'].items():
  if n.endswith('.rs'):
   key=('local/' if receipt['kind']=='extract' else '')+a+'/sources/'+n
   assert key in sources,(a,n);assert sources[key]['sha256']==h,(a,n);rust_checks+=1
 if row['kind']=='kani':
  text=pins[a+'/sources/NDL_SOURCE_PINS.json'];assert isinstance(text,str);assert sha(text.encode())==receipt['source_hashes']['NDL_SOURCE_PINS.json']
  if a=='NDL_K029':
   recovery=json.loads((E/'NDL_K029-lock-recovery.json').read_text());assert receipt['exit_status']==124 and recovery['unchanged_at_first_following_and_recovery'] and recovery['before']==recovery['first_following_before']==recovery['current_recovered_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  else:
   lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  graph=json.loads((E/(a+'-graph-check.json')).read_text());assert graph['graph_matches_frozen'] and not graph['new_package_tuples'] and not graph['edge_errors'] and graph['all_crate_features']
  assert receipt['env']['CARGO_NET_OFFLINE']=='true';assert receipt['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  graphs.append(dict(attempt=a,missing_inactive_roots=graph['missing_package_tuples'],features_recorded=True,post_lock_check='delayed recovery, no credit' if a=='NDL_K029' else 'immediate unchanged'))
 elif row['kind']=='lean':
  if '--deps' in receipt['command']:assert receipt['module']=='NDL_MultiproofInspect' and not receipt['print_axioms']
  else:assert '-M7000' in receipt['command']
audit=json.loads((E/'NDL_L080/receipt.json').read_text());assert audit['exit_status']==0 and len(audit['print_axioms'])==58
modules=json.loads((E/'NDL_AUDIT_THEOREMS.json').read_text())['modules']
for module in modules+['NDL_Audit']:
 latest=next(r for r in reversed(rows) if r['kind']=='lean' and r['module']==module and r['exit_status']==0)
 rc=json.loads((E/latest['attempt']/'receipt.json').read_text());assert sha((E/(module+'.lean')).read_bytes())==rc['source_hashes']['NDL_generated/'+module+'.lean'],module
for line in audit['print_axioms']:
 terms=line.split('[',1)[1].split(']',1)[0].split(', ');assert set(terms)<=set(['propext','Classical.choice','Quot.sound']),line
assert not list(E.rglob('*.rs')),'Rust inputs must be patches/receipts only'
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
assert not subprocess.check_output(['git','diff','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs','Cargo.lock'])
out=dict(attempts=counts,receipts=180,rust_snapshot_hashes=rust_checks,unique_archived_rust_sources=len(patches),graph_lock_feature_checks=graphs,audit_top_theorems=58,standard_axioms_only=True,shipped_source_unchanged=True,files_over_20MiB=0,raw_rust_inputs=0)
(E/'NDL_EVIDENCE_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='graph_lock_feature_checks'}))
