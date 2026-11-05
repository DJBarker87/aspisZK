from pathlib import Path
import subprocess,sys,json,difflib
E=Path(__file__).resolve().parent;mode=sys.argv[1]
r=subprocess.run([sys.executable,str(E/'NHP_dispatch.py'),mode,'short'],capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads((E/'NHP_CURRENT.json').read_text());source=x['source'].replace('#[kani::unwind(8)]','''#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NHP_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NHP_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NHP_KMX::KMX_realloc)]''')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';patch=''
for p in ['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/lib.rs']:
 before=subprocess.check_output(['git','show',rev+':'+p],text=True)
 after=before+'\n#[cfg(kani)]\nmod NHP_dispatch {\n'+source+'}\n' if p.endswith('/pair_forest.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+before+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NHP_KMX;\n'
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NHP_native.patch').write_text(patch);x.update(kind='short splitter explicit KMX bindings',mode=mode,source=source,remaining='arbitrary full production entry/discriminator/rejection-prefix association; K001 error observation retained, frame re-established with explicit KMX binding');(E/'NHP_CURRENT.json').write_text(json.dumps(x,indent=1)+'\n')
print('pair_forest::NHP_dispatch::association')
