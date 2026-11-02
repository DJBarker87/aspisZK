from pathlib import Path
import json,lzma,base64,hashlib,re,subprocess
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();d=json.loads(lzma.decompress((E/'SPLIT-IMMUTABLE-RECOVERY.json.xz').read_bytes()));m={x['path']:x['sha256']for x in d['runs']['K26']['manifest']}
remote='''from pathlib import Path
import json,hashlib
p=Path('/home/dombarker/project-offloads/codex-pv-alib-20261027/PV_AL_SplitFlat.llbc');b=p.read_bytes();d=json.loads(b)
f=next(f for f in d['translated']['files'] if f.get('contents') and f['name']=={'Local':'split-flat-reference.rs'})
print(json.dumps({'artifact_path':str(p),'artifact_sha256':hashlib.sha256(b).hexdigest(),'contents':f['contents']}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=remote,capture_output=True,text=True);assert r.returncode==0,r.stderr;ref=json.loads(r.stdout);b=ref['contents'].encode();assert sha(b)=='478a3dd0f52699baa8a1b8d14f8498adc001400a69dc182280862be6f1495a8d'
assert b==subprocess.check_output(['git','show','ca4a9d3b1c37f921e39154c5b459abf498fe73b0:tools/pv-alib-20261027/split-flat-reference.rs'])
files={n:base64.b64decode(d['files'][h]['base64'])for n,h in m.items()if n.startswith('split/')} # exact selected manifest/module closure
files['KMX_stubs.rs']=base64.b64decode(d['files'][m['KMX_stubs.rs']]['base64']);files['split-flat-reference.rs']=b
p='split/src/lib.rs';old=b'/home/dombarker/project-offloads/codex-pv-kstub-20261028/KMX_stubs.rs';assert old in files[p];files[p]=files[p].replace(old,b'../../KMX_stubs.rs')
p='split/src/sealed.rs';t=files[p].decode();old='/home/dombarker/project-offloads/codex-pv-alib-20261027/split-flat-reference.rs';assert old in t;t=t.replace(old,'../../split-flat-reference.rs')
for name,feature in [('split64_coordinate_lo','negative-lo'),('split64_coordinate_hi','negative-hi')]:
 a=t.index('fn '+name+'(');b=t.index('{',a);i=b;depth=1
 while depth:i+=1;depth+=(t[i]=='{')-(t[i]=='}')
 block=t[a:i+1];old='assert_eq!(blocks.len()*64,rb.len());';assert block.count(old)==1;new='if cfg!(feature="'+feature+'") { assert_ne!(blocks.len()*64,rb.len()); } else { '+old+' }';t=t[:a]+block.replace(old,new)+t[i+1:]
files[p]=t.encode();files['split/Cargo.toml']+=b'\n[features]\nnegative-lo=[]\nnegative-hi=[]\n[workspace]\n'
raw=json.dumps({n:base64.b64encode(b).decode()for n,b in files.items()}).encode();(E/'Split-source.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'Split-source.json.sha256').write_text(sha(raw)+'\n')
(E/'SPLIT-SOURCE-CLOSURE.json').write_text(json.dumps({'credits':['C088','C089'],'immutable_runs':d['runs'],'external_reference_recovery':ref,'external_reference_sha256':sha(ref['contents'].encode()),'reference_generation_receipt':'ca4a9d3b1c37f921e39154c5b459abf498fe73b0:evidence/pv-alib-20261027/charon-split-flat-02/receipt.json','changes':'Only relocate the two absolute module paths into this owned source snapshot and feature-invert each original selected length assertion. Original complete lib/sealed bodies, raw129 input, complementary n<=64/n>64 domains, unwind132, six original KMX stubs retained. No renamed harness or native-step replacement.','limits':'External reference was absent from the broad K26 inventory. Recovered from retained historical LLBC source contents, exactly equal to pinned original Git helper, not copied from a current same-name file. The old C002 no-stub route remains independently suspended under K-1; these are the already-stubbed K26/K28 packets.'},indent=2)+'\n')
for i,h,f,cid in [(19,'split64_coordinate_lo','negative-lo','C088'),(21,'split64_coordinate_hi','negative-hi','C089')]:
 for j in [0,1]:
  cfg={'package':'split-source/split','source_root':'split-source','harness':'sealed::pv_alib_checks::'+h,'features':f if j else '', 'negative':bool(j),'original_credit':cid,'expected_phase':'optimized compilation then bounded complementary split-coordinate comparison, six original pure memory stubs; no field chains','kani_extra':['--no-assertion-reach-checks','-Z','stubbing'],'stubs':['<[u8]>::copy_from_slice','core::ptr::copy_nonoverlapping','<[u8]>::clone_from_slice','Vec::<u8>::extend_from_slice','<[u8]>::to_vec','alloc::alloc::realloc'],'std_transfer':'Original stub/source/native/world qualifications retained; no new deployed std transfer'}
  (E/f'config-K792{i+j:02d}.json').write_text(json.dumps(cfg)+'\n')
print('Prepared the original split lo/hi packets from immutable snapshots and retained LLBC source contents')
