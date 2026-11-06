from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(p.read_bytes())
def raw(p):
 if p.exists():return p.read_bytes()
 if Path(str(p)+'.xz').exists():return lzma.decompress(Path(str(p)+'.xz').read_bytes())
 root=next(x for x in p.parents if x.name.endswith('20261108'));m=root/'NJS_POOLED_INPUTS.json'
 if m.exists():
  v=J(m)[str(p.relative_to(root))];b=lzma.decompress((root/v['pool']).read_bytes());assert H(b)==v['sha256'];return b
 raise FileNotFoundError(p)
kmx=H((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes());rows=[];pairs=[];pins=[];reused=[]
for folder,pre in J(E/'NKC_SPECS.json')[1:]:
 S=E.parent/folder;fs=J(S/f'{pre}_CLOSED.json')['functions'];ats=set()
 for f in fs:
  for pair in f.get('native_pairs',[])+f.get('inherited_native_pairs',[]):
   if not all(a.startswith(pre+'_') for a in pair):reused.append(dict(provider=pre,pair=pair,rows=f['rows']));continue
   pos,neg=pair;ats.update(pair);x=J(S/pos/'receipt.json');y=J(S/neg/'receipt.json');assert x['exit_status']==0 and y['exit_status']==1,pair
   diffs={k:[x['source_hashes'].get(k),y['source_hashes'].get(k)]for k in set(x['source_hashes'])|set(y['source_hashes'])if x['source_hashes'].get(k)!=y['source_hashes'].get(k)}
   pairs.append(dict(positive=pos,negative=neg,source_differences=diffs,rows=f['rows']))
  ats.update(f.get('returned_record_fidelity',[])if pre=='NJY' else [])
 if pre=='NJT':
  shape=J(S/'NJT_QSHAPE_FIDELITY.json');assert shape['status'].startswith('PASS')
  for c in shape['cases']:assert c['actual_exit']==c['expected_exit'];ats.add(c['attempt'])
 for a in sorted(ats):
  # inherited identity record controls are kept in NJQ, checked below.
  if not a.startswith(pre+'_'):continue
  r=J(S/a/'receipt.json');log=raw(S/a/'stdout.log').decode();assert r['exit_status']in [0,1]
  assert ('VERIFICATION:- SUCCESSFUL'in log if r['exit_status']==0 else 'VERIFICATION:- FAILED'in log),a
  assert r['env']['CARGO_NET_OFFLINE']=='true'and str(r['swaps'])=='0'
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  if pre in ['NJS','NJV']:
   v=S/(a+'_validation');g=J(v/'NHR_GRAPH_CHECK.json');lock=J(v/(pre+'_LOCK.json'));inp=J(v/(pre+'_INPUTS.json'));assert inp['KMX_patch_sha256']==kmx
   tg=v/(pre+'_TARGET_GRAPH.json')
   if tg.exists():t=J(tg);assert t['packages_frozen']and t['lock_unchanged']and not t['edge_errors']
  else:g=J(S/(a+'-graph-check.json'));lock=J(S/(a+'-lock-check.json'))
  assert g['graph_matches_frozen']and not g['edge_errors'],a
  assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  rows.append(dict(attempt=a,exit=r['exit_status'],semantic_verification_reached=True,source_revision=r['source_revision'],receipt_sha256=H((S/a/'receipt.json').read_bytes()),source_hashes=r['source_hashes'],frozen_graph=True,unchanged_frozen_lock=True,kmx_sha256=kmx,all_crate_features=g.get('all_features',g.get('features',g.get('selected_closure')))))
# Record-shape controls for raw identity149 are inherited and independently checked.
S=E.parent/'tx2-decoders2-20261108'
for a,expected in [('NJQ_K039',0),('NJQ_K047',1),('NJQ_K056',1),('NJQ_K060',1)]:
 r=J(S/a/'receipt.json');assert r['exit_status']==expected
 log=raw(S/a/'stdout.log').decode();assert ('VERIFICATION:- SUCCESSFUL'in log if expected==0 else 'VERIFICATION:- FAILED'in log)
 pins.append(dict(attempt=a,expected=expected,receipt_sha256=H((S/a/'receipt.json').read_bytes()),semantic_verification_reached=True))
# Preserve all reviewed transcription manifests and source-segment input pins.
rt=J(E.parent/'tx2-decoders3-20261108/NJY_REVIEWED_TRANSCRIPTIONS.json')
assert {x['item']for x in rt['items']}=={'NJY-RT149','NJY-RT152','NJY-RT153','NJY-RT201','NJY-RT203'}
for x in rt['segments']:
 p=E.parent/'tx2-decoders3-20261108'/x['path'];assert H(p.read_bytes())==x['sha256'];pins.append(dict(path=str(p.relative_to(E.parents[1])),sha256=x['sha256']))
(E/'NKC_NATIVE_REVIEW.json').write_text(json.dumps(dict(status='PASS_READ_ONLY_REVALIDATION',new_kani_runs=0,rows=rows,pairs=pairs,reused_native_pairs=reused,identity_record_fidelity=pins[:4],source_segment_pins=pins[4:],reviewed_transcription=rt,copy_patch_sha256=kmx,excluded=['NJY_K041 timeout; NJY_K042 skipped','NJP_K023 excluded','all K2/K3 quarantined or suspended passes'],semantic_transport='P6/D188 option A RECLASSIFICATION; no runtime/cryptographic trust change'),indent=1)+'\n')
print(json.dumps(dict(native_receipts=len(rows),matched_pairs=len(pairs),reused_pairs=len(reused),record_controls=4,source_segments=len(pins)-4)))
