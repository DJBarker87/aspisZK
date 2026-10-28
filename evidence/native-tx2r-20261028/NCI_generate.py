from pathlib import Path
import subprocess,difflib,hashlib,json
E=Path(__file__).resolve().parent
p='crates/aspis-r1-cost-probe/src/verifier.rs'
s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
attrs='''#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,NCI_kmx::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,NCI_kmx::KMX_copy_from_slice)]
'''
h='\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NCI_kmx;\n#[cfg(kani)] mod NCI_reader {\nuse super::*;\n'
for n in [1,4,16,32]:
 for wrong in [False,True]:
  h+=attrs+f'''fn raw{n}_{'wrong' if wrong else 'ok'}(){{
let bytes:[u8;64]=kani::any();let start:usize=kani::any();kani::assume(start<=64-{n});
let mut r=Reader{{bytes:&bytes,at:start}};let out=r.raw::<{n}>();
let k:usize=kani::any();kani::assume(k<{n});
assert!(r.at==start+{n});assert!(r.bytes.as_ptr()==bytes.as_ptr());assert!(r.bytes.len()==64);
assert!({'out[k]!=bytes[start+k]' if wrong else 'out[k]==bytes[start+k]'});
}}\n'''
h+='}\n'
patch=Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_text()+''.join(difflib.unified_diff(s.splitlines(True),(s+h).splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NCI_reader.patch').write_text(patch)
(E/'NCI_PATCH_PINS.json').write_text(json.dumps({'KMX_sha256':hashlib.sha256(Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest(),'reader_patch_sha256':hashlib.sha256(patch.encode()).hexdigest(),'source_sha256':hashlib.sha256(s.encode()).hexdigest()},indent=2)+'\n')
