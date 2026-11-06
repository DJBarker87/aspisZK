from pathlib import Path
import json,hashlib,lzma,subprocess,base64
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'};LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef';KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
def raw(p):
 if p.is_file():return p.read_bytes()
 q=Path(str(p)+'.xz')
 if q.is_file():
  b=lzma.decompress(q.read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
 if 'batch-merkle3-20261108'in str(p):
  d=E.parent/'batch-merkle3-20261108';refs=json.loads((d/'NKL_POOLED_INPUTS.json').read_text());name=str(p.relative_to(d))
  if name in refs:
   x=refs[name];b=(d/x['file']).read_bytes()if 'file'in x else lzma.decompress((d/x['pool']).read_bytes());assert len(b)==x['bytes']and H(b)==x['sha256'];return b
 return subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(E.parent.parent))])
def J(p):return json.loads(raw(p))
checks=[];pairs=[];failures=[]
for folder,pre in [('circle-points','NKM'),('terminal4','NKI'),('batch-merkle3','NKL'),('tx2-adapters2','NKP')]:
 p=E.parent/(folder+'-20261108');fs=J(p/f'{pre}_CLOSED.json')['functions'];ps={tuple(pair)for f in fs for pair in f['native_pairs']}
 # Explicit boundary/shape/copy controls also consumed by circle split route.
 if pre=='NKM':ps|={('NKM_K026','NKM_K028'),('NKM_K012','NKM_K013'),('NKM_K014','NKM_K015'),('NKM_K014','NKM_K016'),('NKM_K011','NKM_K003')}
 names={n for pair in ps for n in pair}
 for n in sorted(names):
  d=p if n.startswith(pre)else E.parent/'terminal2-20261108'
  r=J(d/n/'receipt.json');log=raw(d/n/'stdout.log').decode();gpath=d/(n+'-graph-check.json');lpath=d/(n+'-lock-check.json')
  if pre=='NKL':gpath=d/(n+'_validation/NHR_GRAPH_CHECK.json');lpath=d/(n+'_validation/NKL_LOCK.json')
  g=J(gpath);l=J(lpath);assert r['limits']==LIMITS and r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',n
  assert g['graph_matches_frozen']and not g.get('edge_errors')and not g.get('added'),n
  assert l['unchanged']and l['before']==l['after']==LOCK,n
  a=J(d/(n+'-admission.json'));assert a['exit']==0 and a['reservation']['allowed']is True,n
  assert r['exit_status']in [0,1]and 'VERIFICATION:- '+('SUCCESSFUL'if r['exit_status']==0 else'FAILED')in log,n
  if r['exit_status']:assert 'Failed Checks:'in log or 'is assignable'in log,n
  checks.append(dict(provider=pre,attempt=n,exit=r['exit_status'],receipt_sha256=H(raw(d/n/'receipt.json')),graph_sha256=H(raw(gpath)),lock_sha256=H(raw(lpath)),source_hashes=r['source_hashes'],native_command=r.get('native_command'),deployed_feature_receipt=g.get('selected_closure',g.get('features')),metadata_features=r.get('metadata_features')))
 for pair in sorted(ps):
  a=next(x for x in checks if x['attempt']==pair[0]);b=next(x for x in checks if x['attempt']==pair[1]);assert a['exit']==0 and b['exit']==1,pair
  common=set(a['source_hashes'])&set(b['source_hashes']);src=[k for k in common if k.endswith(('.rs','.rs.txt'))]
  if not src:src=[k for k in common if any(w in k for w in ['SOURCE_PINS.json','EXTRA_INPUTS.json','STAGING_MANIFEST.json'])]
  assert src,pair
  for k in src:
   if a['source_hashes'][k]!=b['source_hashes'][k]:
    if pre=='NKP':
     ca=J(p/(pair[0]+'_CUT.json'));cb=J(p/(pair[1]+'_CUT.json'));assert ca['kind']==cb['kind']and ca['field']==cb['field'];assert [e[0]for e in ca['edits']]==[e[0]for e in cb['edits']]
     assert J(p/(pair[0]+'-erasure-check.json'))['passed']and J(p/(pair[1]+'-erasure-check.json'))['passed']
     assert ca['instrumented_sha256']==H(ca['edits'][0][1].encode())and cb['instrumented_sha256']==H(cb['edits'][0][1].encode())
     continue
    assert pair==('NKM_K026','NKM_K028') and k=='NKM_SOURCE_PINS.json',(pair,k)
    aa=J(p/'NKM_SPLIT_OVERLAY.json');bb=J(p/'NKM_FINAL_OVERLAY.json');av=base64.b64decode(aa['data']);bv=base64.b64decode(bb['data']);guard=b' if cfg!(NKM_control_add){kani::assume(kind==1&&a==QM31::ZERO&&b==QM31::ZERO);}' + bytes([10]);assert bv.replace(guard,b'')==av
    pa=J(p/'NKM_K026/sources/NKM_SOURCE_PINS.json');pb=J(p/'NKM_K028/sources/NKM_SOURCE_PINS.json');diff=[k for k in pa if pa[k]!=pb.get(k)];assert diff==['crates/aspis-r1-cost-probe/src/NKM_native.rs'];assert H(av)==pa[diff[0]]and H(bv)==pb[diff[0]]
    assert 'NKM_control_add'not in J(p/'NKM_K026/receipt.json')['env']['RUSTFLAGS'] and 'NKM_control_add'in J(p/'NKM_K028/receipt.json')['env']['RUSTFLAGS']

  pairs.append(dict(provider=pre,positive=pair[0],control=pair[1],common_direct_or_manifest_source_pins_identical=(pre!='NKP'and pair!=('NKM_K026','NKM_K028')),NKP_control_mutates_selected_field_before_good=(pre=='NKP'),control_difference='Exact cfg-disabled-in-positive zero-add valid-domain restriction, same harness/event/assertion and KMX; NKW_NKM_BOUNDARY_CONTROL.diff'if pair==('NKM_K026','NKM_K028')else None))
patch=raw(Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch'));assert H(patch)==KMX
(E/'NKW_NATIVE_REVIEW.json').write_text(json.dumps(dict(status='PASS_READ_ONLY_RECEIPT_REVALIDATION',checks=checks,pairs=pairs,copy_patch_sha256=KMX,excluded=['NKM_K025 TIMEOUT','NKM_K027 TIMEOUT','NKL_K073/NKL_K075 excluded controls'],kani_launched=0,extraction_launched=0,quarantined_Option_fn=[],suspended_writable_static=[],interpretation='No native field arithmetic proof credited. Natural-spec assumptions paired with named emitted Lean laws; arbitrary-reply native parent specialized in Lean. Wrapper value evidence does not prove allocation identity.'),indent=1)+'\n');print(json.dumps(dict(native_receipts=len(checks),matched_pairs=len(pairs),status='PASS')))
