"""Audit the six current NEE rows using their active replacement certificates."""
from NEK_scan import *
D=read_json(ROOT/'evidence/slice-s-compose2-20261029/NEE_LEDGER_DELTA.json');out=[]
for fn,c in D['members'].items():
 if not fn.endswith(('::transfer_common','::withdrawal_common','::digest_is_canonical')):continue
 evidence=[]
 for x in c['native_association']:
  p=ROOT/x['path'];assert sha(p.read_bytes())==x['sha256'],x
  if p.name!='receipt.json':continue
  r=read_json(p);attempt=r['attempt'];patch=ROOT/f'evidence/slice-s-compose2-20261029/{attempt}-NEE_native_contracts.patch'
  expected=r['source_hashes']['NEE_native_contracts.patch'];assert sha(patch.read_bytes())==expected
  o=dict(patched_files(patch.read_text()));assert o
  assert all(not re.search(r'\bstatic\s+mut\b',t) for t in o.values())
  # The pure module in each exact contract patch is separate from all oracle
  # storage; the loaded path is named and its complete contents are hashed.
  selected=[(n,t) for n,t in o.items() if n.endswith('NEE_payment_frames.rs')];assert len(selected)==1
  assert all(not re.search(r'\bstatic\b|\bUnsafeCell\b|\bAtomic\w*\b',t) for _,t in selected)
  graph=read_json(ROOT/f'evidence/slice-s-compose2-20261029/{attempt}-graph-check.json')
  patch_hash=r['source_hashes']['NEE_KMX_copy_stubs.patch'];assert patch_hash=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  evidence.append(dict(receipt=str(p.relative_to(ROOT)),receipt_sha256=sha(p.read_bytes()),exit=r['exit_status'],harness=r['module'],contract_patch_sha256=expected,source_hashes={n:sha(t.encode()) for n,t in o.items()},feature_graph_sha256=sha((ROOT/f'evidence/slice-s-compose2-20261029/{attempt}-graph-check.json').read_bytes()),storage='exact selected pure module has no writable statics',scope='K-3 unaffected active replacement; retained tool/source/shape qualifications'))
 assert len(evidence)==2 and [e['exit'] for e in evidence]==[0,1]
 out.append(dict(function=fn,certificate=c['id'],certified_active_support=evidence,legacy_receipts='retained baseline history is inventoried separately; it is not the current certificate native association',k3_status='CLEARED_ACTIVE_SUPPORT',remaining_inner_hypotheses=c['inner_hypotheses_remaining']))
(E/'NEK_NEE_ACTIVE_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',len(out),'functions / six transaction occurrence rows; no replay of unaffected support')
