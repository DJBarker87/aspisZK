"""Resume same-name native properties; controls change one asserted equality."""
from NEH_extra import *

def remember(rp,pos,neg):
 p=E/'NEH_NEW_CONTROL_PAIRS.json';pairs=read_json(p) if p.exists() else []
 item=dict(original_receipt=rp,positive=pos,control=neg)
 if item not in pairs:pairs.append(item)
 p.write_text(json.dumps(pairs,indent=2)+'\n')

def nbg():
 # These four complete original modules are already static-free. No field
 # multiplication or global logging is reached by these selected functions.
 n='crates/aspis-core/src/field/NBG_runtime.rs'
 tasks=[(7,'assert!(a.a.0==add(x.a.0,y.a.0) && a.b.0==add(x.b.0,y.b.0));'),(6,'assert!(x.add(y).0==add(x.0,y.0));'),(8,'assert!(a.c0.a.0==add(x.c0.a.0,y.c0.a.0) && a.c0.b.0==add(x.c0.b.0,y.c0.b.0));'),(12,'assert!(c.a.0==a.0 && c.b.0==b.0);')]
 for i,(num,assertion) in enumerate(tasks):
  rp=f'evidence/native-tx2c-20261027/NBG_K{num:03}/receipt.json';patch=ROOT/Path(rp).parent.parent/(f'NBG_K{num:03}-harness.patch');o=dict(patched_files(patch.read_text()));assert n in o
  assert assertion in o[n]
  for neg in [False,True]:
   a=f'NEH_K{76+2*i+int(neg):03}'
   if (E/a/'receipt.json').exists():continue
   changed=dict(o)
   if neg:changed[n]=o[n].replace(assertion,'assert!(!('+assertion[len('assert!('):-2]+'));',1)
   publish(a,rp,changed,neg)
  remember(rp,f'NEH_K{76+2*i:03}',f'NEH_K{77+2*i:03}')
if __name__=='__main__':nbg()

def nbq(start=84):
 p='crates/aspis-r1-cost-probe/src/fast_pairing.rs';src=dict(patched_files((ROOT/'evidence/native-tx2h-20261028/NBQ_K001-harness.patch').read_text()))[p]
 startmod=src.index('    #[cfg(kani)]\n    mod NBQ_private');brace=src.index('{',startmod);depth=1;i=brace+1
 while depth:
  if src[i]=='{':depth+=1
  if src[i]=='}':depth-=1
  i+=1
 module=src[startmod:i]
 for j,(num,name,assertion) in enumerate([(1,'reduce_all','assert!(u64::from(r)==x%u64::from(P));'),(2,'new','assert!(d.sums==[0;4]);')]):
  rp=f'evidence/native-tx2h-20261028/NBQ_K{num:03}/receipt.json'
  for neg in [False,True]:
   a=f'NEH_K{start+2*j+int(neg):03}'
   if (E/a/'receipt.json').exists():continue
   b=module
   if neg:b=b.replace(assertion,'assert!(!('+assertion[len('assert!('):-2]+'));',1)
   b=b.replace('#[kani::proof]', '#[kani::proof] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NEH_kmx::KMX_copy_nonoverlapping)]')
   raw=frozen(p).decode();# Insert at the original canonical module's closing brace.
   # Original patch retained exact context before canonical's final brace.
   marker='\n}\n\n\n///'
   # Locate canonical braces structurally; preserve every original source byte.
   at=raw.index('{',raw.index('mod canonical'));d=1;k=at+1
   while d:
    if raw[k]=='{':d+=1
    if raw[k]=='}':d-=1
    k+=1
   raw=raw[:k-1]+b+'\n'+raw[k-1:]
   o=root_overlay('crates/aspis-r1-cost-probe','NEH_kmx','extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));');o[p]=raw
   publish(a,rp,o,neg)
  remember(rp,f'NEH_K{start+2*j:03}',f'NEH_K{start+2*j+1:03}')

def common(start=88):
 from NEH_migrate_common import migrate
 c=read_json(ROOT/'evidence/slice-s-leaves-20261029/NEC_CLOSED.json')[0]
 pairs=list(zip(c['kani_receipt_paths'],c['control_receipts']))[2:]
 for i,rp in enumerate([v for pair in pairs for v in pair]):
  a=f'NEH_K{start+i:03}'
  if (E/a/'receipt.json').exists():continue
  out=migrate(rp);patch=str(Path(rp).parent/'NDM_harness.patch')
  with (E/(a+'-driver.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NEH_replay.py'),a,rp,patch],env={**os.environ,'NEH_OVERLAY_FILE':str(out)},stdout=f,stderr=subprocess.STDOUT)
  print(a,rp,r.returncode,flush=True)
  if r.returncode:raise SystemExit('own input fault; inspect before continuing')
  t=(E/a/'stdout.log').read_text();v='OPEN' if 'timed out' in t.lower() else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in t else 'FAIL' if 'VERIFICATION:- FAILED' in t else 'OPEN'
  with (E/'NEH_REPLAY_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,original_receipt=rp,verdict=v,expected='PASS' if i%2==0 else 'FAIL',method='direct local native observation; original contract composition remains open'))+'\n')
  if (i%2==0 and v=='FAIL') or (i%2==1 and v=='PASS'):
   with (E/'NEH_FINDINGS.md').open('a') as f:f.write(f'\nLocal observation finding {a} / {rp}: {v}; original composition credit remains suspended.\n')

def split_constructor(start=112):
 rp='evidence/native-tx2h-20261028/NBQ_K002/receipt.json'
 o=read_json(E/'NEH_K086_overlay.json');n='crates/aspis-r1-cost-probe/src/fast_pairing.rs'
 old='assert!(d.sums==[0;4]);';new='assert!(d.sums[0]==0 && d.sums[1]==0 && d.sums[2]==0 && d.sums[3]==0);'
 assert o[n].count(old)==1
 for neg in [False,True]:
  a=f'NEH_K{start+int(neg):03}';changed=dict(o)
  changed[n]=o[n].replace(old,new if not neg else 'assert!(!(d.sums[0]==0 && d.sums[1]==0 && d.sums[2]==0 && d.sums[3]==0));')
  if not (E/a/'receipt.json').exists():publish(a,rp,changed,neg)
 remember(rp,f'NEH_K{start:03}',f'NEH_K{start+1:03}')

def ndt_copy(start=114):
 for i,num in enumerate([8,9]):
  rp=f'evidence/native-front2-20261028/NDE_K{num:03}/receipt.json';r=read_json(ROOT/rp);ni=r.get('native_command') or r['command'];manifest=ni[ni.index('--manifest-path')+1];suffix=manifest.split('_src/')[1].removesuffix('/Cargo.toml');h=r.get('module') or ni[ni.index('--harness')+1];mod=h.split('::')[0]
  o=root_overlay(suffix,mod,'extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));')
  a=f'NEH_K{start+i:03}'
  if not (E/a/'receipt.json').exists():publish(a,rp,o,i==1)
 p=E/'NEH_EXTRA_PAIRS.json';pairs=read_json(p) if p.exists() else []
 pair=[f'evidence/native-front2-20261028/NDE_K{n:03}/receipt.json' for n in [8,9]]
 if pair not in pairs:pairs.append(pair)
 p.write_text(json.dumps(pairs,indent=2)+'\n')

def knf(start=116):
 # Preserve the original standalone crate filename, module names and sources.
 base=ROOT/'evidence/kani-k2leaf-20261028'
 field=(base/'KNF_field.rs').read_text();wide=(base/'KNF_wide_exact.rs').read_text();audit=[]
 for i,num in enumerate([4,5,6,7,8]):
  rp=f'evidence/kani-k2leaf-20261028/KNF_K{num:03}/receipt.json';r=read_json(ROOT/rp);h=r['selected_harness'];a=f'NEH_K{start+i:03}'
  source=(base/f'sources/KNF_K{num:03}.rs').read_text()
  for name,data in [('KNF_harness.rs',source),('KNF_field.rs',field),('KNF_wide_exact.rs',wide)]:assert sha(data.encode())==r['source_hashes'][name],(rp,name)
  body=source.replace('#[kani::proof]', '#[kani::proof] #[kani::stub(core::ptr::copy_nonoverlapping,NEH_kmx::KMX_copy_nonoverlapping)]')
  body='#![feature(allocator_api)]\n'+body+'\nextern crate alloc;\nmod NEH_kmx {include!("KMX_stubs.rs");}\n'
  o={'KNF_harness.rs':body,'KNF_field.rs':field,'KNF_wide_exact.rs':wide}
  cmd=['/home/dombarker/.kani/kani-0.67.0/bin/kani-driver',B+'/NEH_src/KNF_harness.rs','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--harness',h,'--output-format','regular','--solver','kissat','-Z','concrete-playback','--concrete-playback','print','--cbmc-args','--unwinding-assertions','--slice-formula']
  path=E/(a+'_native_template.json');path.write_text(json.dumps(cmd,indent=2)+'\n')
  os.environ['NEH_NATIVE_TEMPLATE']=str(path);os.environ['NEH_STANDALONE']='1'
  if not (E/a/'receipt.json').exists():publish(a,rp,o,num in [5,7])
  del os.environ['NEH_NATIVE_TEMPLATE'];del os.environ['NEH_STANDALONE']
  audit.append(dict(attempt=a,original_receipt=rp,original_hashes=r['source_hashes'],method='original standalone filename and names, original arbitrary-prestate single transition, identical field helper bytes, exact KMX ptr stub',limitation='K-3 only; existing standalone/native association qualifications unchanged'))
 p=E/'NEH_EXTRA_PAIRS.json';pairs=read_json(p) if p.exists() else []
 for positive,control in [(4,5),(6,7)]:
  pair=[f'evidence/kani-k2leaf-20261028/KNF_K{n:03}/receipt.json' for n in [positive,control]]
  if pair not in pairs:pairs.append(pair)
 p.write_text(json.dumps(pairs,indent=2)+'\n');(E/'NEH_KNF_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
