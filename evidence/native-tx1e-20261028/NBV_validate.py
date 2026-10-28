from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
patch=(R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
block=patch.split('+++ b/KMX_stubs.rs\n',1)[1].split('diff --git',1)[0]
stub=''.join(l[1:] for l in block.splitlines(True) if l.startswith('+') and not l.startswith('+++'))
stub_sha=hashlib.sha256(stub.encode()).hexdigest();patch_sha=hashlib.sha256(patch.encode()).hexdigest()
NEG={2,8,14,15,17,19,21,29,31,33,35,37,41,43,45,47,49,50}
rows=[];errors=[]
for p in sorted(E.glob('NBV_[KL][0-9][0-9][0-9]/receipt.json')):
 rc=json.loads(p.read_text());a=rc['attempt'];text=(p.parent/'stdout.log').read_text();kind=rc['kind']
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert str(rc['swaps'])=='0',a
 ad=json.loads((E/(a+'-reservation.json')).read_text());assert ad['allowed'] is True,a
 for f,digest in rc['source_hashes'].items():
  snapshot=p.parent/'sources'/f
  assert snapshot.exists(),(a,'missing source snapshot',f)
  assert hashlib.sha256(snapshot.read_bytes()).hexdigest()==digest,(a,f)
 status='pass' if rc['exit_status']==0 else 'excluded'
 if kind=='kani':
  assert rc['source_hashes']['NBV_src/KMX_stubs.rs']==stub_sha,(a,'KMX Rust replacement drift')
  assert rc['source_hashes']['NBV_KMX_copy_stubs.patch']==patch_sha,(a,'KMX patch drift')
  g=json.loads((E/(a+'-graph.json')).read_text());assert g['allowed'] and not g['new_packages'] and not g['edge_errors'] and g['unchanged'],a
  assert g['lock_before']==g['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  timed='timed out' in text.lower() or rc['exit_status']==124
  number=int(a[-3:])
  failed=[b for b in re.split(r'(?=\nCheck \d+:)',text) if '- Status: FAILURE' in b]
  if timed:status='timeout'
  elif number in NEG:
   assert rc['exit_status']!=0 and failed,(a,'negative control failed for no proved assertion')
   assert all('.assertion.' in b.split('\n\t - Status:')[0] for b in failed),(a,'negative control failed non-assertion',failed)
   status='expected-negative-fail'
  elif number==1:
   assert 'error[E0583]' in text and rc['exit_status']!=0
   status='pre-proof-input-error'
  else:assert rc['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in text,(a,'unexpected failed property')
 elif rc['exit_status']==0:
  assert rc['print_axioms'],a
  for line in rc['print_axioms']:
   assert not any(x in line for x in ['sorryAx','native_decide','axiomOf']),line
   ax=re.search(r'axioms: \[(.*?)\]',line)
   if ax:assert set(ax.group(1).split(', '))<= {'propext','Classical.choice','Quot.sound'},line
  status='standard-axioms-pass'
 else:status='rejected-draft'
 rows.append(dict(attempt=a,status=status,exit=rc['exit_status'],wall=rc['wall_seconds'],peak_rss_kib=int(rc['peak_rss_kib']),swaps=rc['swaps'],source_revision=rc['source_revision'],source_hashes=rc['source_hashes']))
assert sum(r['attempt'].startswith('NBV_K') for r in rows)<=50
assert sum(r['attempt'].startswith('NBV_L') for r in rows)<=100
for p in (R/'docs/research/100bit-spend-path-20261013/lean').glob('NBV_*.lean'):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',p.read_text()),p
out=dict(attempts=rows,totals={status:sum(r['status']==status for r in rows) for status in sorted({r['status'] for r in rows})},wall_seconds=sum(r['wall'] for r in rows),max_peak_rss_kib=max(r['peak_rss_kib'] for r in rows),all_swap_zero=True,errors=errors)
(E/'NBV_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='attempts'}))
