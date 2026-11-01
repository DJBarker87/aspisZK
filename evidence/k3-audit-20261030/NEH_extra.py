from NEH_verdict import verdict as parse_verdict
from NEH_replay import *
from NEH_scan import frozen, read_json
import difflib

def publish(a,rp,o,negative=False):
 # New negative controls invert an existing value equality, never rename it.
 fn=E/(a+'_overlay.json');fn.write_text(json.dumps(o,indent=2)+'\n')
 patch=E/(a+'_harness.patch');diff=[]
 for n,t in o.items():
  old=frozen(n);diff.extend(difflib.unified_diff((old or b'').decode().splitlines(True),t.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
 patch.write_text(''.join(diff))
 with (E/(a+'-driver.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NEH_replay.py'),a,rp,str(patch.relative_to(ROOT))],env={**os.environ,'NEH_OVERLAY_FILE':str(fn),'NEH_KMX_REQUIRED':'1'},stdout=f,stderr=subprocess.STDOUT)
 print(a,rp,r.returncode,flush=True)
 if r.returncode:raise SystemExit('own input fault; inspect')
 q=read_json(E/a/'receipt.json');t=(E/a/'stdout.log').read_text();v=parse_verdict(t)
 with (E/'NEH_REPLAY_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,original_receipt=rp,verdict=v,expected='FAIL' if negative else 'PASS',new_control=negative))+'\n')
 if (negative and v=='PASS') or (not negative and v=='FAIL'):
  with (E/'NEH_FINDINGS.md').open('a') as f:f.write(f'\nImmediate replay finding {a}: {rp}, got {v}. Original harness name and native function preserved.\n')
 return v

def root_overlay(root,mod,body):
 n=root+'/src/lib.rs';return {n:'#![cfg_attr(kani, feature(allocator_api))]\n'+frozen(n).decode()+'\n#[cfg(kani)] mod '+mod+' {\n'+body+'\n}\n'}

def extras():
 todo=[]
 # Highest direct-row fanout copy-control contexts, in order. Read sources only.
 pairs=[('evidence/native-front2-20261028',8,9),('evidence/native-front3b-20261028',5,6),('evidence/native-front3-20261028',22,23),('evidence/native-front3b-20261028',12,13),('evidence/native-front4b-20261028',1,2)]
 for directory,p,c in pairs:
  prefix={'native-front2-20261028':'NDE','native-front3b-20261028':'NDI','native-front3-20261028':'NDF','native-front4b-20261028':'NDM'}[Path(directory).name]
  for num in [p,c]:
   rp=f'{directory}/{prefix}_K{num:03}/receipt.json';r=read_json(ROOT/rp);ni=r.get('native_command') or r['command'];manifest=ni[ni.index('--manifest-path')+1];suffix=manifest.split('_src/')[1].removesuffix('/Cargo.toml');h=r.get('module') or ni[ni.index('--harness')+1];mod=h.split('::')[0]
   if 'KMX_checks' in h:body='extern crate alloc; include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));'
   else:
    group=next(q for q in read_json(E/'NEH_APPLICABILITY.json')['receipts'] if q['receipt']==rp);m=next(v for n,v in group['matched_sources'].items() if n.endswith('/'+mod+'.rs'))['source'];assert '::' not in m,m;body=(ROOT/m).read_text()
   todo.append((rp,root_overlay(suffix,mod,body),num==c))
 # One high-fanout native projection member, plus a same-name falsification.
 rp='evidence/native-tx2b-20261027/NBD_K009/receipt.json';p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';m='crates/aspis-statement/src/pool_v1/NBD_terminal.rs';t=dict(patched_files((ROOT/'evidence/native-tx2b-20261027/NBD_harness.patch').read_text()))[m]
 for negative in [False,True]:
  b=t.replace('#[kani::proof]','#[kani::proof] #[kani::unwind(40)]\n#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEH_kmx::KMX_copy_nonoverlapping)]')
  if negative:b=b.replace('assert!(core::ptr::eq(s.common(),common_ref));','assert!(!core::ptr::eq(s.common(),common_ref));')
  o=root_overlay('crates/aspis-statement','NEH_kmx','extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));');o.update({p:frozen(p).decode()+'\n#[cfg(kani)] mod NBD_terminal;\n',m:b});todo.append((rp,o,negative))
 # Scalar private reducer/constructor/finish; omit unrelated global-log modules.
 p='crates/aspis-r1-cost-probe/src/fast_pairing.rs';t=dict(patched_files((ROOT/'evidence/native-tx2h-20261028/NBQ_K001-harness.patch').read_text()))[p];start=t.index('    #[cfg(kani)]\n    mod NBQ_private');end=t.index('\n\n }',start) if '\n\n }' in t[start:] else -1
 # Extract the exact original inner module using brace balance.
 brace=t.index('{',start);depth=1;i=brace+1
 while depth:
  if t[i]=='{':depth+=1
  if t[i]=='}':depth-=1
  i+=1
 module=t[start:i]
 for num,name in [(1,'reduce_all'),(2,'new'),(3,'finish')]:
  rp=f'evidence/native-tx2h-20261028/NBQ_K{num:03}/receipt.json'
  for negative in [False,True]:
   b=module
   if negative:
    if name=='reduce_all':b=b.replace('assert!(u64::from(r)==x%u64::from(P));','assert!(u64::from(r)!=x%u64::from(P));')
    if name=='new':b=b.replace('assert!(d.sums==[0;4]);','assert!(d.sums!=[0;4]);')
    if name=='finish':b=b.replace('assert!(u64::from(q[0])==s[0]%u64::from(P));','assert!(u64::from(q[0])!=s[0]%u64::from(P));')
   b=b.replace('#[kani::proof]', '#[kani::proof] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NEH_kmx::KMX_copy_nonoverlapping)]')
   raw=frozen(p).decode();mark='    pub const P:u32=0x7fff_ffff;';raw=raw.replace(mark,b+'\n'+mark)
   o=root_overlay('crates/aspis-r1-cost-probe','NEH_kmx','extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));');o[p]=raw
   todo.append((rp,o,negative))
 assert len(todo)==18,len(todo)
 paired=[]
 for i,(rp,o,neg) in enumerate(todo):
  a=f'NEH_K{100+i:03}'
  if not (E/a/'receipt.json').exists():publish(a,rp,o,neg)
  paired.append(dict(attempt=a,original_receipt=rp,negative=neg))
 (E/'NEH_EXTRA_MAP.json').write_text(json.dumps(paired,indent=2)+'\n')
 (E/'NEH_EXTRA_PAIRS.json').write_text(json.dumps([[todo[i][0],todo[i+1][0]] for i in range(0,10,2)],indent=2)+'\n')
if __name__=='__main__':extras()
