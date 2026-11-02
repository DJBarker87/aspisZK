from NEK_controls import *
def run():
 for i,(directory,p,c,prefix) in enumerate([('native-front3b-20261028',5,6,'NDI'),('native-front4b-20261028',1,2,'NDM')]):
  for j,num in enumerate([p,c]):
   a=f'NEK_K{(305 if prefix=="NDI" else 309)+j:03}'
   if (E/a/'receipt.json').exists():continue
   rp=f'evidence/{directory}/{prefix}_K{num:03}/receipt.json';r=read_json(ROOT/rp);ni=r.get('native_command') or r['command'];manifest=ni[ni.index('--manifest-path')+1];suffix=manifest.split('_src/')[1].removesuffix('/Cargo.toml');h=r.get('module') or ni[ni.index('--harness')+1];mod=h.split('::')[0]
   from NEK_recover import recover
   ss,missing=recover(rp);assert not missing,missing
   body=next(t for n,t in ss.items() if n.endswith('/'+mod+'.rs')) if 'KMX_checks' not in h else 'extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));'
   o=root(suffix,mod,body)
   v=publish(a,rp,o,num==c,'original KMX/configuration control, only static-free selected module compiled')
   if v=='OPEN':return
if __name__=='__main__':run()
