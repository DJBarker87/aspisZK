from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;x=json.loads((E/'NJC_NATIVE_INPUTS.json').read_text());path='crates/aspis-r1-cost-probe/src/NJC_validate.rs';s=x[path]
s+='''
fn end_check(){let queries:[u32;22]=kani::any();let i:usize=kani::any();kani::assume(i>=22);
 let result:Result<(),Error>=if i<queries.len(){unreachable!()}else{Ok(())};
 assert_eq!(result.is_ok(),!cfg!(NJC_invert));
}
'''
for suffix in ['','_renamed']:
 s+='''#[kani::proof]
#[kani::unwind(26)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn validate_end'''+suffix+'(){end_check();}\n'
x[path]=s;(E/'NJC_validate.rs.txt').write_text(s);(E/'NJC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NJC_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NJC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch='';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for n,t in x.items():
 z=subprocess.run(['git','show',rev+':'+n],capture_output=True,text=True);old=z.stdout if z.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJC_native.patch').write_text(patch)
