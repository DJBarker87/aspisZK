from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent
x=json.loads((E/'NJC_NATIVE_INPUTS.json').read_text());old='crates/aspis-r1-cost-probe/src/NJC_weight_step.rs';original=(E/'NJC_K020/sources/NJC_src'/old).read_text();x[old]=original;(E/'NJC_weight_step.rs.txt').write_text(original);path='crates/aspis-r1-cost-probe/src/NJC_weight_end.rs';s=original[:original.index('#[kani::proof]')]
s+='''
fn end_check(){
 let bytes:[u8;16]=kani::any();let before:[[u32;4];64]=kani::any();
 let mut values:[K;64]=core::array::from_fn(|i|make(before[i]));
 let j:usize=kani::any();kani::assume(j<64);let at:usize=kani::any();
 let reply=step(&bytes,at,&mut values[64..]);
 assert_eq!(reply,Ok(at^(if cfg!(NJC_invert){1}else{0})));
 assert_eq!(words(values[j]),before[j]);
}
'''
for suffix in ['','_renamed']:
 s+='''#[kani::proof]
#[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn weight_end'''+suffix+'(){end_check();}\n'
x[path]=s;(E/'NJC_weight_end.rs.txt').write_text(s)
v='crates/aspis-r1-cost-probe/src/verifier.rs';assert 'mod NJC_weight_end;' not in x[v];x[v]+='\n#[cfg(kani)]\n#[path="NJC_weight_end.rs"]\nmod NJC_weight_end;\n'
(E/'NJC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
pins=json.loads((E/'NJC_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});(E/'NJC_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch='';rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
for n,t in x.items():
 z=subprocess.run(['git','show',rev+':'+n],capture_output=True,text=True);old=z.stdout if z.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJC_native.patch').write_text(patch)
