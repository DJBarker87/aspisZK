"""Inspect copy source and emitted backward continuations; no native run."""
from pathlib import Path
import json,subprocess,shlex,hashlib,sys
E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
root='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/'
anchors=[('core/src/slice/mod.rs','pub const fn copy_from_slice(&mut self, src: &[T])'),
 ('core/src/slice/mod.rs','const unsafe fn copy_from_slice_impl<T: Clone>(dest: &mut [T], src: &[T])'),
 ('core/src/slice/index.rs','unsafe impl<T> const SliceIndex<[T]> for ops::Range<usize>'),
 ('core/src/slice/index.rs','unsafe impl<T> const SliceIndex<[T]> for ops::RangeTo<usize>'),
 ('core/src/slice/index.rs','unsafe impl<T> const SliceIndex<[T]> for ops::RangeFrom<usize>')]
code='''from pathlib import Path
import sys,json,hashlib
x=json.load(sys.stdin);out=[]
for path,anchor in x['anchors']:
 p=Path(x['root']+path);raw=p.read_bytes();s=raw.decode();a=s.index(anchor);i=s.index('{',a);j=i+1;n=1
 while n:
  n+=(s[j]=='{')-(s[j]=='}');j+=1
 out.append(dict(path=path,anchor=anchor,file_sha256=hashlib.sha256(raw).hexdigest(),text=s[a:j]))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(root=root,anchors=anchors)),text=True,capture_output=True)
assert r.returncode==0,r.stderr
rows=json.loads(r.stdout)
assert 'if dest.len() != src.len()' in rows[1]['text']
assert 'ptr::copy_nonoverlapping(src.as_ptr(), dest.as_mut_ptr(), dest.len())' in rows[1]['text']
source=subprocess.check_output(['git','show','HEAD:docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean'],text=True)
a=source.index('def\n  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body');b=source.index('/--',a);body=source[a:b]
for text in ['let a5 := to_slice_mut_back s4','let field_mask_entropy1 := deref_mut_back a5','let a7 := to_slice_mut_back1 s7','let leaf_salt_seed1 := deref_mut_back1 a7','let bytes1 := as_mut_back s1']:assert text in body
out=dict(evidence_class='D188 source inspection plus local source-value laws; physical copy association remains P',rust_version='1.94.1',sources=rows,emission_sha256=sha(source.encode()),body_sha256=sha(body.encode()),body=body,restoration='all original-fill and both copied-array backward continuations are applied; none discarded',retained=['no native differential under inherited zero-native budget','actual source-frame addresses and nonaliasing','intrinsic/runtime memcpy semantics and machine copies under V370/L3','all full-entry/allocator/diagnostic/callback and privacy obligations'],trust_fields_added=[],rows_removed=[])
p=E/'entropy-copy-restoration.json'
if '--check' in sys.argv:assert json.load(open(p))==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS original and both copy restorations retained; physical/source-frame association OPEN')
