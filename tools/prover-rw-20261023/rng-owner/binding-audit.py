"""Read-only source/translation normalization audit; no builds or new laws."""
from pathlib import Path
import hashlib,json,re,sys
D=Path(__file__).resolve().parent;R=D.parents[2];P=D.parent/'rng-preflight'
L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-owner'
pin=lambda s:dict(sha256=hashlib.sha256(s).hexdigest(),bytes=len(s))
native=(R/'crates/aspis-prover/src/state_only_entropy.rs').read_text()
a=native.index('    pub fn generate_for_mask_nonce(');b=native.index('    pub fn mask_nonce(',a)
old=native[a:b].replace('pub fn generate_for_mask_nonce(','pub fn old(').replace('mask_nonce: [u8; 32],','mask_nonce: [u8; 32],\n        tape: &mut Tape,',1).replace('getrandom::fill(bytes.as_mut())?;','tape.draw(&mut bytes)?;')
prototype=(D/'prototype/lib.rs').read_text()
assert old in prototype
assert (P/'prototype/lib.rs').read_text().split('#[cfg(test)]')[0] in prototype
llbcpath=Path(sys.argv[1]);raw=llbcpath.read_bytes();data=json.loads(raw)['translated']
assert data['files'][0]['contents']==prototype
entries=[]
for f in data['fun_decls']:
 if not f:continue
 m=f['item_meta']
 if not m['is_local']:continue
 source=m.get('source_text') or ''
 entries.append(dict(name=m['name'],signature=pin(json.dumps(f['signature'],sort_keys=True).encode()),source=pin(source.encode()),span=m['span'],opacity=m['opacity'],body_present=f.get('body') is not None))
assert entries and all(e['opacity']=='Transparent' for e in entries)
def clean(s):
 # All generated documentation comments are unnested in these inputs.
 s=re.sub(r'/\-[\s\S]*?\-/','',s);s=re.sub(r'--[^\n]*','',s)
 return re.sub(r'@\[[\s\S]*?\]','',s)
def defs(s):
 s=clean(s);starts=list(re.finditer(r'(?m)^\s*(?:def|structure|inductive|class)\s+(\S+)',s));out={}
 for i,m in enumerate(starts):
  end=starts[i+1].start() if i+1<len(starts) else len(s)
  decl=s[m.start():end];decl=decl.split('\nend ')[0]
  out[m[1]]=re.sub(r'\s+','',decl)
 return out
common=[]
for name in ['Types.lean.txt','Funs.lean.txt']:
 before=defs((P/'generated'/name).read_text());after=defs((D/'generated'/name).read_text())
 for n in before.keys() & after.keys():
  assert before[n]==after[n],(name,n)
  common.append(dict(declaration=n,normalized_sha256=pin(before[n].encode())['sha256']))
assert len(common)>=7,common
# Full retained borrowed control is mechanically selected verbatim by adapt.py.
f=(D/'generated/Funs.lean.txt').read_text();tail=f[f.index('/-- [prover_rw_rng_owner::{impl core::convert::From'):]
assert (L/'ProverRwRngOwnerEmission.lean').read_text().endswith(tail)
result=dict(schema='rng-owner-source-coverage-v1',base='ece5baabbc9c975d631aae8d5ca716e28ad4f268',native_source=pin(native.encode()),native_owner=pin(native[a:b].encode()),adapted_borrowed_owner=pin(old.encode()),prototype=pin(prototype.encode()),llbc=pin(raw),llbc_embedded_source_matches=True,local_transparent_declarations=entries,common_declarations_identical=common,retained_borrowed_control_verbatim=True,source_coverage=['nonce scan','cap16 guard','fresh zero64 input','one indexed mutable draw including error partial writes','two32-byte copies','short circuit two nonzero tests','success private bytes','retry checked increment','error conversion Os(u8)','provider return through every native-prototype status'],trust_boundary=['existing Charon/Aeneas/runtime primitive extraction policy','transparent value-level Zeroizing new/deref installation','unused ErasureFns; no physical cleanup theorem','u8 error tag substitution; no native getrandom::Error layout or E1 association'],historical_kani=dict(reused_for_universal=False,reason='stronger Lean source-body correspondence and bounded source loop induction; no Kani-to-Lean axiom',domain='prior count<128; cap16 from zero gives at most16 and checked increment <=17<65536; historical_cut_sufficient proves numerical sufficiency only'),native_source_changed=False)
(E/'source-coverage.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(local_declarations=len(entries),common_defs=len(common),llbc=result['llbc'])))
