"""Full finite static-data comparison on unchanged Rust 1.94.1 source.
Native compilation is the expected cost; no field arithmetic or elimination.
This does not alone establish the complete structural row binding.
"""
from pathlib import Path
import json,hashlib,re,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src')
bundle=json.load(open(D/'v260-native-inputs.json'));records=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def frozen(p):
 j=bundle['files'][p];b=(S/p).read_bytes();assert sha(b)==j['sha256'],p
 records.append(dict(path=p,sha256=j['sha256'],blob=j['blob'],native_path=str(S/p)))
 return b.decode()
transport=frozen('crates/aspis-core/src/r0/transport.rs')
pads=frozen('crates/aspis-core/src/r0/transport_pads.rs')
mod=frozen('crates/aspis-core/src/r0/mod.rs')
assert 'pub const MESSAGE_LEN: usize = 1024;' in mod
assert 'pub type Message<E> = [E; MESSAGE_LEN];' in mod
assert '#[cfg' not in transport and '#[cfg' not in pads
source='''#[allow(dead_code)]
mod r0 {
 pub const MESSAGE_LEN: usize = 1024;
 pub type Message<E> = [E; MESSAGE_LEN];
 #[path=PATH] pub mod transport;
}
fn main() {
 assert_eq!(usize::BITS,64);
 println!("{:?}",r0::transport::COEFFICIENT_TO_ROW);
}
'''.replace('PATH',json.dumps(str(S/'crates/aspis-core/src/r0/transport.rs')))
(D/'v260-constant-probe.rs').write_text(source)
rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
cmd=[rustc,'--edition=2021','--cfg','feature="ct-host-prover"','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no',str(D/'v260-constant-probe.rs'),'-o',str(D/'v260-constant-probe')]
subprocess.run(cmd,check=True)
values=json.loads(subprocess.check_output([str(D/'v260-constant-probe')],text=True))
table=bundle['files']['docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2_C_Table.lean']['text']
chunks={int(n):[int(x) for x in re.findall(r'(\d+)#u16',body)] for n,body in re.findall(r'def chunk(\d+) : List U16 := \[([^]]*)\]',table)}
assert sorted(chunks)==list(range(32)) and all(len(v)==32 for v in chunks.values())
expr=table.split('def values : List U16 :=',1)[1].split('\ntheorem',1)[0]
# Accept only the complete append expression; no other operation can be hidden.
toks=re.findall(r'chunk\d+|\+\+|[()]|\S',expr)
def parse_atom(i):
 if toks[i]=='(':
  seq,k=parse_expr(i+1);assert toks[k]==')';return seq,k+1
 assert re.fullmatch(r'chunk\d+',toks[i]),toks[i]
 return [int(toks[i][5:])],i+1
def parse_expr(i):
 seq,k=parse_atom(i)
 while k<len(toks) and toks[k]=='++':
  rest,k=parse_atom(k+1);seq+=rest
 return seq,k
order,k=parse_expr(0);assert k==len(toks) and order==list(range(32))
lean=[x for n in order for x in chunks[n]]
assert values==lean and len(values)==1024
bad=lean.copy();bad[0],bad[1]=bad[1],bad[0];assert values!=bad
opening=frozen('crates/aspis-core/src/r0/opening.rs')
body=opening.split('pub const COPY_ACTIVE_ROW_MASKS:',1)[1].split('=',1)[1].split('[',1)[1].split(']',1)[0]
assert re.fullmatch(r'[\s\d,]+',body)
masks=[int(x) for x in re.findall(r'\d+',body)]
funs=bundle['files']['docs/research/v8-r0-zk-20261009/lean/R1Z/PV_B2_C_RawWeights253Funs.lean']['text']
body=funs.split('def aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS',1)[1].split('Array.make',1)[1].split('[',1)[1].split(']',1)[0]
model_masks=[int(x) for x in re.findall(r'(\d+)#u16',body)]
assert masks==model_masks and len(masks)==64
result=dict(command=cmd,source_revision=bundle['revision'],input_pins=records,adapter_source=source,adapter_argument='Only the exact parent MESSAGE_LEN and Message aliases are supplied; native transport.rs and its included pads are unchanged, not copied or edited',table_entries=len(values),mask_entries=len(masks),native_table=values,model_table=lean,negative_control='swapped first two entries rejected',rustc=subprocess.check_output([rustc,'-vV'],text=True),binary_sha256=sha((D/'v260-constant-probe').read_bytes()),features_context='Retained deployed per-crate feature graph; reached transport source has no cfg/cfg!, compiled with ct-host-prover and the deployed release settings',feature_graph_sha256=sha((D/'deployed-client-features.json').read_bytes()),evidence_class='exhaustive equality of static data under existing pinned compiler tool trust; not a proof of LLVM or complete row binding',composition='reclassification within existing tool trust; zero endpoint premise removal')
(D/'v260-constants-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('All 1024 native/model transport entries and 64 mask literals match; changed-table control rejected; complete row binding still required')
