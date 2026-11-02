from pathlib import Path
import subprocess,json,lzma,base64,hashlib
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();credits=json.loads(lzma.decompress((E/'CREDITS.json.xz').read_bytes()));files={};records=[]
manifest=subprocess.check_output(['git','show','4bc172e539c065040181e74fc281135f73e422ec:tools/pv-cb-20261026/proof/Cargo.toml'])
for cid,package,features,old,new in [
 ('C017','push','negative-push','assert_eq!(actual.as_bytes(),&[a,b]);','if cfg!(feature="negative-push") { assert_ne!(actual.as_bytes(),&[a,b]); } else { assert_eq!(actual.as_bytes(),&[a,b]); }'),
 ('C016','pop','negative-pop','assert_eq!(old,expected.copied());','if cfg!(feature="negative-pop") { assert_ne!(old,expected.copied()); } else { assert_eq!(old,expected.copied()); }'),
 ('C013','empty','negative-empty','assert_eq!(actual.is_empty(),reference::empty(&bytes[..len]));','if cfg!(feature="negative-empty") { assert_ne!(actual.is_empty(),reference::empty(&bytes[..len])); } else { assert_eq!(actual.is_empty(),reference::empty(&bytes[..len])); }')]:
 x=next(x for x in credits if x['credit_id']==cid);inp=next((n,v)for n,v in x['matched_sources'].items()if n.endswith('/proof/lib.rs'));h=inp[1]['sha256'];b=(E/'blobs'/(h+'.rs')).read_bytes();t=b.decode();assert t.count(old)==1,(cid,old);t=t.replace(old,new);files[package+'/lib.rs']=t.encode();files[package+'/Cargo.toml']=manifest+f'\n[features]\n{features}=[]\n'.encode()
 r=next(v['sha256']for n,v in x['matched_sources'].items()if n.endswith('/proof/reference.rs'));files[package+'/reference.rs']=(E/'blobs'/(r+'.rs')).read_bytes()
 records.append({'credit':cid,'harness':x['harness'],'root_original_sha256':h,'reference_sha256':r,'manifest_sha256':sha(manifest),'change':features+' selects only the assertion inversion. Complete original root/reference, names/bounds/domains unchanged.'})
raw=json.dumps({n:base64.b64encode(b).decode()for n,b in files.items()}).encode();(E/'Standalone-source.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'Standalone-source.json.sha256').write_text(sha(raw)+'\n');(E/'STANDALONE-SOURCE-CLOSURE.json').write_text(json.dumps(records,indent=2)+'\n')
