from pathlib import Path
import json,lzma,base64,hashlib
E=Path(__file__).resolve().parent;P=E/'caller';OLD=E.parent/'pv-k3scan-20261101';sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads(lzma.decompress((OLD/'Padding-source.json.xz').read_bytes()))
f={n:base64.b64decode(b) for n,b in x.items() if n.startswith('native/')}
p='native/digest-0.10.7/src/core_api/wrapper.rs';orig=f[p].decode();(E/'wrapper.frozen.rs').write_text(orig)
# Instrument only the core child edge of the builtin field-ordered Default derive.
needle='    /// Create new wrapper from `core`.'
method='''    /// K-3 local context: field-ordered derived Default caller with core child intercepted.
    pub fn pv_context_default<F: FnOnce() -> T>(oracle: F) -> Self {
        Self { core: oracle(), buffer: Default::default() }
    }

'''
assert orig.count(needle)==1
f[p]=orig.replace(needle,method+needle).encode()
raw=json.dumps({n:base64.b64encode(b).decode() for n,b in f.items()}).encode();(E/'default-source.json.xz').write_bytes(lzma.compress(raw));(E/'default-source.json.sha256').write_text(sha(raw)+'\n')
p=P/'Cargo.toml';t=p.read_text().replace('[profile.dev]','digest="=0.10.7"\n[patch.crates-io]\ndigest={path="../native/digest-0.10.7"}\nblock-buffer={path="../native/block-buffer-0.10.4"}\n[profile.dev]');p.write_text(t)
(P/'default.rs').write_text('''use digest::core_api::{BlockSizeUser,BufferKindUser,CoreWrapper};
use digest::typenum::U64;
#[derive(Clone,Copy,Debug,Eq,PartialEq)] struct Core([u32;8]);
impl BlockSizeUser for Core {type BlockSize=U64;}
impl BufferKindUser for Core {type BufferKind=digest::block_buffer::Eager;}
struct Log {calls:usize,reply:Core,frame:[u32;8]}
// Full return type Core, arbitrary raw limbs. Modifies only calls/reply; frame preserved.
fn oracle(log:&mut Log)->Core {
 let reply=Core(kani::any());log.calls+=1;log.reply=reply;reply
}
#[kani::proof] #[kani::unwind(70)]
fn wrapper_default_arbitrary_core() {
 let frame:[u32;8]=kani::any();let mut log=Log{calls:0,reply:Core([0;8]),frame};
 let native=CoreWrapper::<Core>::pv_context_default(|| oracle(&mut log));
 let (core,buffer)=native.decompose();
 let expected=if cfg!(feature="negative-control") {Core([log.reply.0[0]^1,log.reply.0[1],log.reply.0[2],log.reply.0[3],log.reply.0[4],log.reply.0[5],log.reply.0[6],log.reply.0[7]])} else {log.reply};
 assert_eq!(core,expected);assert_eq!(buffer.pv_dl_bytes(),&[0;64]);assert_eq!(buffer.get_pos(),0);
 assert_eq!(log.calls,1);assert_eq!(log.frame,frame);
}
''')
p=P/'lib.rs';p.write_text(p.read_text()+'\n#[path="default.rs"] mod generic_default_gate;\n')
for i,n in [(91909,False),(91910,True)]:
 (E/f'config-K{i}.json').write_text(json.dumps({'harness':'generic_default_gate::wrapper_default_arbitrary_core','credit':'C053','negative':n},indent=2)+'\n')
(E/'DEFAULT-BOUNDARY.json').write_text(json.dumps({'native_origin':'digest 0.10.7 CoreWrapper<T>, derive(Clone,Default)','wrapper_sha256':sha(orig.encode()),'instrumentation':'adds a method with field-ordered initializer; first Default child replaced by FnOnce oracle with a captured local &mut Log; buffer child remains actual Default','unconstrained_reply':'Core([u32;8]) all raw limbs; no seed constraint','modifies':['local Log.calls','local Log.reply'],'frame':['local Log.frame','all external memory'],'borrowed_returns':False,'restoration_gate':'requires checked derived Default expansion association, actual Core::default seeded-read bridge and existing model substitution; a caller PASS alone does not restore C053'},indent=2)+'\n')
