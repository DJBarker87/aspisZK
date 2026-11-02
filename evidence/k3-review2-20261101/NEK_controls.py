"""Recheck selected KMX configurations without unrelated static harness modules."""
from NEK_priority import *
def controls(start=15):
 pairs=[('evidence/native-front2-20261028',8,9),('evidence/native-front3b-20261028',5,6),('evidence/native-front3-20261028',22,23),('evidence/native-front4b-20261028',1,2)]
 index=start
 for directory,p,c in pairs:
  prefix={'native-front2-20261028':'NDE','native-front3b-20261028':'NDI','native-front3-20261028':'NDF','native-front4b-20261028':'NDM'}[Path(directory).name]
  for num in [p,c]:
   a=f'NEK_K{index:03}';index+=1
   if (E/a/'receipt.json').exists():continue
   rp=f'{directory}/{prefix}_K{num:03}/receipt.json';r=read_json(ROOT/rp);ni=r.get('native_command') or r['command'];manifest=ni[ni.index('--manifest-path')+1];suffix=manifest.split('_src/')[1].removesuffix('/Cargo.toml');h=r.get('module') or ni[ni.index('--harness')+1];mod=h.split('::')[0]
   if 'KMX_checks' in h:body='extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));'
   else:
    from NEK_recover import recover
    sources,missing=recover(rp);assert not missing,missing
    body=next(t for n,t in sources.items() if n.endswith('/'+mod+'.rs'))
   o=root(suffix,mod,body)
   publish(a,rp,o,num==c,'exact KMX/configuration control, unrelated static modules omitted; no writable static in compiled harness closure')
if __name__=='__main__':controls(int(sys.argv[1]) if len(sys.argv)>1 else 15)
