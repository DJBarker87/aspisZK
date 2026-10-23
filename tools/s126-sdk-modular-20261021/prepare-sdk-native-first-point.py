#!/usr/bin/env python3
"""Original SDK first-entry cut: initial bytes at reached child calls and return.
No owned reference or SDK model executes. Compare is a pure arbitrary choice,
so both real comparison outcomes are included. Full typed common child replies
and empty successful first result remain explicit cut/installation boundaries.
"""
from pathlib import Path
import json,hashlib,subprocess,sys
R=Path(__file__).resolve().parents[2];out=Path(sys.argv[1]);root=int(sys.argv[2]);assert 0<=root<3
window=int(sys.argv[3]) if root==0 else None
if root==0:assert 0<=window<15
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-first-ordinary.py'),str(out),'native'],check=True)
p=out/'src/lib.rs';s=p.read_text()
a=s.index(' if unsafe{CALLS.value[0][0]}==1 {');b=s.index(' kani::cover!(',a)
s=s[:a]+s[b:]
a=s.index(' kani::cover!(');b=s.index('\n}\n}',a)
s=s[:a]+''' kani::cover!(unsafe{CALLS.value[0]}==[1,1,1,1],"original SDK reaches exact first call");
 kani::cover!(unsafe{CALLS.value[0]}==[1,1,1,1]&&initial_counts[0]==isize::MAX-1,"first entry at maximum permitted proof shared counter");'''+s[b:]
for line in ['mod sdk_live_models;\n','use aspis_s126_owned_sdk_borrowed as owned;\n','use owned::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk};\n']:
 assert line in s;s=s.replace(line,'')
assert 'owned::' not in s and '#[kani::stub(AccountInfo::' not in s
a=s.index('fn plan()->')
s=s[:a]+'''static mut FRAME_ROOT:GhostStorage<usize>=GhostStorage{value:0,allocation_tag:0x51a7000000000001};
static mut FRAME_INDEX:GhostStorage<usize>=GhostStorage{value:0,allocation_tag:0x51a7000000000002};
static mut FRAME_BYTE:GhostStorage<u8>=GhostStorage{value:0,allocation_tag:0x51a7000000000003};
fn frame_probe(){
 let root=unsafe{FRAME_ROOT.value};let index=unsafe{FRAME_INDEX.value};assert!(root<3);
 assert!(index<[58295,1880,1768][root]);
 assert_eq!(unsafe{NATIVE_ROOT_PTRS.value[root].add(index).read()},unsafe{FRAME_BYTE.value},"original SDK first-prefix byte equals initial input at every reached boundary");
}
'''+s[a:]
signatures=[
 'fn planned_decode(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{',
 'fn planned_validate(statement:&PoolV1PairForestTerminalStatementV1)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{',
 'fn planned_encode(afterstate:&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{',
 'fn planned_tx1<H:aspis_core::Digest32>(public:Public<\'_>,bytes:&[u8],proof:&[u8],k:usize,_:H,observer:verifier::Observer)->Result<Vec<u8>,verifier::Error>{',
 '#[no_mangle] pub extern "C" fn s126_coupled_cmp(a:*const u8,b:*const u8,n:usize)->i32 {']
for sig in signatures:
 assert s.count(sig)==1,sig;s=s.replace(sig,sig+'\n frame_probe();')
needle=' let pointers=core::array::from_fn::<_,3,_>(|i|buffers[i].as_ptr());';assert s.count(needle)==1
selection=f' let selected_root:usize={root};\n'
if root==0:selection+=f' let offset:u16=kani::any();let selected_index:usize={4096*window}+(offset%4096) as usize;kani::assume(selected_index<buffers[selected_root].len());\n'
else:selection+=' let selected_index:usize=kani::any();kani::assume(selected_index<buffers[selected_root].len());\n'
selection+=''' let lengths=core::array::from_fn::<_,3,_>(|i|buffers[i].len());
 let capacities=core::array::from_fn::<_,3,_>(|i|buffers[i].capacity());
 unsafe{FRAME_ROOT.value=selected_root;FRAME_INDEX.value=selected_index;FRAME_BYTE.value=buffers[selected_root][selected_index];}
'''
s=s.replace(needle,needle+'\n'+selection)
needle=' assert_eq!(amounts,initial_amounts);';assert s.count(needle)==1
s=s.replace(needle,needle+'''
 frame_probe();
 for i in 0..3{assert_eq!(buffers[i].as_ptr(),pointers[i]);assert_eq!(buffers[i].len(),lengths[i]);assert_eq!(buffers[i].capacity(),capacities[i]);}
''')
line='#[kani::stub(aspis_s126_owned_sdk_borrowed::decode_public_statement_box,planned_decode)]\n';assert line in s;s=s.replace(line,'')
line='#[kani::stub(aspis_s126_owned_sdk_borrowed::owned_checkpoint_nonzero,planned_scan)]\n';assert line in s;s=s.replace(line,'')
p.write_text(s)
p=out/'Cargo.toml';c=p.read_text();c='\n'.join(x for x in c.splitlines() if not x.startswith('aspis-s126-owned-sdk-borrowed='))+'\n'
name=f'first-frame-root{root}'+(f'-window{window}' if root==0 else '')+'-v1'
c=c.replace('first-coupling-v3',name);p.write_text(c)
p=out/'source-cut.json';m=json.loads(p.read_text());m.update(source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,observer_root=root,observer_window=window,window_start=4096*window if window is not None else None,window_width=4096 if window is not None else None,events=['decoder','validator','encoder','comparison','first/tx1','returned error'],remaining='Every source probe/assertion/safety/unwinding property plus both covers must pass. Need all proof windows/root cases on identical source/harness domain and existing index/list coverage. No whole native frame assumed; no SDK model substitution. Actual scan/comparison/source-child cut instances, successful first-output/writeback continuation, runtime/oracle/global joins remain explicit.')
p.write_text(json.dumps(m,indent=2)+'\n')
