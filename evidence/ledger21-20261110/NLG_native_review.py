from pathlib import Path
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();seen={};checks=[];pairs=[]
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef';KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
def raw(p):
 if p.is_file():return p.read_bytes()
 if Path(str(p)+'.xz').is_file():
  b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
 d=next((q for q in p.parents if q.parent==E.parent),None)
 if d:
  pre=d.name
  if pre=='tx2-resume-20261108':
   idx=json.loads((d/'NKK_INPUT_INDEX.json').read_text());key=str(p.relative_to(d))
   if key in idx:
    row=idx[key];b=lzma.decompress((d/row['capsule']).read_bytes());assert H(b)==row['sha256'];return b
 if d and d.name=='tx2-native6-20261108':
  idx=json.loads(subprocess.check_output(['git','show','HEAD:'+str((d/'NJJ_INPUTS_INDEX.json').relative_to(E.parent.parent))]));key=str(p.relative_to(d))
  if key in idx:
   row=idx[key];z=d/row['archive'];b=lzma.decompress(subprocess.check_output(['git','show','HEAD:'+str(z.relative_to(E.parent.parent))]));assert H(b)==row['sha256'];return b
 return subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(E.parent.parent))],stderr=subprocess.DEVNULL)
def J(p):return json.loads(raw(p))
def receipt(d,a,positive):
 key=(str(d),a)
 if key in seen:return seen[key]
 r=J(d/a/'receipt.json');log=raw(d/a/'stdout.log').decode();g=J(d/(a+'-graph-check.json'));l=J(d/(a+'-lock-check.json'));ad=J(d/(a+'-admission.json'))
 assert r['limits']==LIMITS and r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
 assert g['graph_matches_frozen'] and not g.get('edge_errors') and l['unchanged']and l['before']==l['after']==LOCK,a
 assert ad['exit']==0 and ad['reservation']['allowed']is True,a
 assert r['exit_status']==(0 if positive else 1)and 'VERIFICATION:- '+('SUCCESSFUL'if positive else'FAILED')in log,a
 features={z['name']:set(z['features'])for z in g['selected_closure']}
 assert {'default','optimized-terminal','private-leaf-salts','program-build'}<=features['aspis-r1-cost-probe'],a
 assert {'r0','pool-v1-kernel'}<=features['aspis-statement'] and len([f for f in features['aspis-statement']if f.endswith('-audit')])==12,a
 if 'aspis-r1-cost-probe-program'in features:assert {'pool-adapter','private-leaf-salts'}<=features['aspis-r1-cost-probe-program'] and 'no-entrypoint'not in features['aspis-r1-cost-probe-program'],a
 erasure=None
 if d.name=='row-bridges-20261109':
  erasure=J(d/(a+'-erasure-check.json'));assert erasure['passed']and not erasure['changed'],a
 # Every original input is retained and its receipt hash checked.
 verified=[]
 for n,h in r['source_hashes'].items():
  if d.name=='row-bridges-20261109':
   idx=J(d/'NKY_INPUTS.json');obj=idx['objects'][h];z=d/obj['path'];assert H(z.read_bytes())==obj['archive_sha256'];b=lzma.decompress(z.read_bytes())
  else:
   candidates=[d/a/'sources'/n,d/n];b=None
   for p in candidates:
    try:q=raw(p)
    except(subprocess.CalledProcessError,FileNotFoundError):continue
    if H(q)==h:b=q;break
   assert b is not None,(a,n,'missing retained hash')
  assert H(b)==h,(a,n)
  verified.append(dict(source=n,sha256=h,bytes=len(b)))
 x=dict(attempt=a,positive=positive,exit=r['exit_status'],receipt_sha256=H(raw(d/a/'receipt.json')),graph_sha256=H(raw(d/(a+'-graph-check.json'))),lock_sha256=H(raw(d/(a+'-lock-check.json'))),source_inputs=verified,deployed_feature_parity_checked=True,erasure_sha256=H(raw(d/(a+'-erasure-check.json')))if erasure else None,selected_features=g.get('selected_closure'),all_features=g.get('all_features'),copy_patch_sha256=KMX)
 seen[key]=x;checks.append(x);return x
# NKU consumes this exact pre-existing table; K045 is variant-only and never used for Prepared payload.
p=E.parent/'tx2-resume2-20261109';table=J(p/'NKU_NATIVE_CUT_TABLE.json')
for pin in J(p/'NKU_INPUT_PINS.json'):assert H(raw(E.parent.parent/pin['path']))==pin['sha256']
for row in table['rows']:
 d=(E.parent.parent/row['positive_receipt']).parent.parent
 receipt(d,row['positive'],True)
 for ctl in row['controls']:
  receipt(d,ctl,False);pairs.append(dict(positive=row['positive'],control=ctl,harness=row['harness'],domain=row['domain']))
# Full Prepared/Accumulator native tail is required; K045 only covers variant.
d=E.parent/'tx2-native6-20261108'
for row in J(d/'NJJ_NATIVE_CERTIFICATES.json'):
 if row['harness'].split('::')[-1] not in ['prepared_tail','accumulator_tail']:continue
 receipt(d,row['positive'],True)
 for ctl in row['controls']:
  receipt(d,ctl,False);pairs.append(dict(positive=row['positive'],control=ctl,harness=row['harness'],domain='Full native constructor fields and SAME owned allocation'))
# NKY final positives and semantic mutations; K001/K014 excluded.
d=E.parent/'row-bridges-20261109'
for positive,controls in [(8,[9,10]),(11,[12,13]),(15,[16,17]),(18,[19,20]),(21,[22,23]),(24,[25,26])]:
 a=f'NKY_K{positive:03}';receipt(d,a,True)
 for n in controls:
  c=f'NKY_K{n:03}';receipt(d,c,False);pairs.append(dict(positive=a,control=c))
# Levels and raw decoder reuse input packets are themselves immutable and fully hash checked.
for name in ['NKY_LEVELS_REUSE.json','NKY_NKP_REUSE.json']:
 x=J(d/name)
 if 'rows'in x:
  for row in x['rows']:
   for s in row['sources']:
    z=E.parent.parent/s['path'];b=raw(z);b=lzma.decompress(b)if z.suffix=='.xz'and H(b)!=s['sha256']else b;assert H(b)==s['sha256']
 else:
  for row in x['inputs']:
   z=E.parent.parent/row['archive'];assert H(lzma.decompress(z.read_bytes()))==row['sha256']
assert H(raw(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'))==KMX
out=dict(status='PASS_READ_ONLY_RECEIPT_REVALIDATION',checks=checks,pairs=pairs,kani_launched=0,extraction_launched=0,copy_patch_sha256=KMX,excluded=['NKY_K001 validation failure','NKY_K014 memcmp unwind failure','NKK_K045 Prepared variant only: payload uses native prepared_tail cut instead'],Option_fn_credit=[],writable_static_credit=[],classification='Existing P6/D188 option-A native transport RECLASSIFICATION; never trust removal')
(E/'NLG_NATIVE_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status='PASS',receipts=len(checks),pairs=len(pairs))))
