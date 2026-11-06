from pathlib import Path
import json,lzma,hashlib,re
E=Path(__file__).resolve().parent;P=E.parent/'terminal5-20261108';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
J=lambda p:json.loads(raw(p))
pairs=J(P/'NKR_NATIVE_PAIRS.json')['pairs'];checks={};rows=[]
for pair in pairs:
 for pos,k in [(True,'positive'),(False,'negative')]:
  a=pair[k]
  if a in checks:continue
  r=J(P/a/'receipt.json');g=J(P/(a+'-graph-check.json'));lock=J(P/(a+'-lock-check.json'));ad=J(P/(a+'-admission.json'))
  assert H(raw(P/a/'receipt.json'))==pair[k+'_receipt_sha256']
  assert r['exit_status']==(0 if pos else 1)
  assert g['graph_matches_frozen'] and not g['edge_errors'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert ad['exit']==0 and ad['reservation']['allowed']is True
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  features={v['name']:set(v['features'])for v in g['selected_closure']}
  if 'aspis-r1-cost-probe' in features:assert {'default','optimized-terminal','private-leaf-salts','program-build'}<=features['aspis-r1-cost-probe']
  assert {'r0','pool-v1-kernel'}<=features['aspis-statement'] and sum(v.endswith('-audit')for v in features['aspis-statement'])==12
  assert r['source_hashes']['NKR_KMX.patch']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  log=raw(P/a/'stdout.log').decode();assert 'VERIFICATION:- '+('SUCCESSFUL'if pos else'FAILED')in log
  checks[a]=dict(receipt_sha256=H(raw(P/a/'receipt.json')),graph_sha256=H(raw(P/(a+'-graph-check.json'))),lock_sha256=H(raw(P/(a+'-lock-check.json'))),exit=r['exit_status'],positive=pos,features={k:sorted(v)for k,v in features.items()},source_hashes=r['source_hashes'])
 for n,h in pair['same_input_hashes'].items():
  # Receipt snapshots bind the exact evidence used, not later mutable copies.
  for a in [pair['positive'],pair['negative']]:assert J(P/a/'receipt.json')['source_hashes'][n]==h
 rows.append(pair)
assert J(P/'NKR_NATIVE_RELEASE.json')['all_receipt_inputs_hash_checked']
(E/'NLO_NATIVE_REVIEW.json').write_text(json.dumps(dict(status='PASS_RETAINED_PAIRS_REVALIDATED',pairs=rows,checks=checks,native_runs=0,copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',NLN='No new Kani: NLL/NKV retained native folds; THIS gate replays full universal Result/array/log/abort packets',classification='ReviewedTranscription under existing P6/D188 option-A reclassification; never removal',Option_fn_credit=[],writable_static_credit=[]),indent=1)+'\n')
print(json.dumps(dict(pairs=len(rows),receipts=len(checks),status='PASS')))
