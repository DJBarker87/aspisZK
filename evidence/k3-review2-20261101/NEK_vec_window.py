"""Strictly split NCN timeout: one arbitrary byte window, direct owned pre-state.
No whole certificate credit: matched control, exact copy admission, Vec shape
controls and native/Lean byte assembly remain required even if this passes.
"""
from NEK_priority import *
def run():
 a='NEK_K344';rp='evidence/native-tx2r2-20261028/NCN_K061/receipt.json';o=read_json(E/'NEK_K031_overlay.json');p='crates/aspis-r1-cost-probe/src/verifier.rs';t=o[p]
 target='pub(super) fn row(raw:&Vec<[u64;4]>,index:usize)->[u64;4]{raw[index]}'
 replacement='pub(super) fn row(raw:&Vec<[u64;4]>,index:usize,window:(usize,u32))->[u64;4]{raw[index]}'
 assert t.count(target)==1;t=t.replace(target,replacement)
 old='#[kani::ensures(|out:&[u64;4]| *out==raw[index])]'
 new='#[kani::requires(window.0<4&&window.1<8)]\n#[kani::ensures(|out:&[u64;4]| ((out[window.0] >> (8*window.1)) & 255)==((raw[index][window.0] >> (8*window.1)) & 255))]'
 assert t.count(old)==1;t=t.replace(old,new)
 t=t.replace('NCN_vec::row(&self.raw,index)','NCN_vec::row(&self.raw,index,(0,0))').replace('row(&raw,index)','row(&raw,index,(0,0))')
 start=t.index('fn row_contract()');brace=t.index('{',start);i=brace+1;d=1
 while d:d+=(t[i]=='{')-(t[i]=='}');i+=1
 body=t[brace+1:i-1]
 # Same arbitrary 64-row values and index domain. Transfer one Box allocation
 # into Vec with the identical allocation layout, avoiding Vec::from's large
 # copy graph. No initialized element is dropped or invented.
 body=body.replace('let raw=Vec::from(rows);','let owned=alloc::boxed::Box::new(rows);let raw=unsafe{Vec::from_raw_parts(alloc::boxed::Box::into_raw(owned) as *mut [u64;4],64,64)};')
 body=body.replace('let _=row(&raw,index,(0,0));','let window:(usize,u32)=kani::any();let _=row(&raw,index,window);')
 t=t[:brace+1]+body+t[i-1:];o[p]=t
 v=publish(a,rp,o,False,'strict arbitrary byte-window split of NCN row contract; direct Box-to-Vec ownership pre-state; no native composition credit until window/control/copy/shape/assembly gates close')
 (E/'NEK_VEC_WINDOW_STATUS.json').write_text(json.dumps(dict(attempt=a,verdict=v,status='OPEN',remaining=['same-window failing control','official-copy same-configuration admission','borrowed Vec interface fidelity controls','UInt64 byte-window assembly and native/Lean association'],domain='all 64 arbitrary rows; arbitrary valid row, limb and byte indices; no caller narrowing',allocation='Box<[[u64;4];64]> to Vec<[u64;4]>: same allocation size 2048, alignment 8, capacity 64, unique ownership'),indent=2)+'\n')
if __name__=='__main__':run()
