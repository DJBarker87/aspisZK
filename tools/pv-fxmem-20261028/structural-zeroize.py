"""Token gate over zeroize 1.8.1; no binary erasure claim."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
p='/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/zeroize-1.8.1/src/lib.rs'
r=subprocess.run(['ssh','dombarker@100.108.41.90','cat '+p],text=True,capture_output=True);assert r.returncode==0,r.stderr
s=r.stdout
# Same complete-body parser/tokenizer as the already reviewed drop gate.
src=(R/'tools/pv-fxmem-20261028/structural-drop.py').read_text();a=src.index('def clean(');b=src.index('expected=');exec(src[a:b])
expected=[('impl<Z> Drop for Zeroizing<Z>','{fn drop(&mut self) {self.0.zeroize()}}'),('impl<Z> Zeroize for Z','{fn zeroize(&mut self) {volatile_write(self, Z::default());atomic_fence();}}'),
 ('impl<Z, const N: usize> Zeroize for [Z; N]','{fn zeroize(&mut self) {self.iter_mut().zeroize();}}'),
 ("impl<Z> Zeroize for IterMut<'_, Z>",'{fn zeroize(&mut self) {for elem in self {elem.zeroize();}}}'),
 ('fn atomic_fence()','{atomic::compiler_fence(atomic::Ordering::SeqCst);}'),
 ('fn volatile_write<T: Copy + Sized>(dst: &mut T, src: T)','{unsafe {ptr::write_volatile(dst, src)}}')]
checks=[]
for anchor,want in expected:
 actual=body(s,anchor);assert tokens(actual)==tokens(want),(anchor,actual)
 checks.append(dict(anchor=anchor,body=actual,tokens_equal=True,line=s[:s.index(anchor)].count('\n')+1))
assert tokens(body(s,'impl_zeroize_with_default! {'))==tokens('{PhantomPinned, (), bool, char, f32, f64, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize}')
j=dict(evidence_class='structural (K-1 substitute)',path=p,sha256=hashlib.sha256(s.encode()).hexdigest(),checks=checks,
 establishes='At source level every byte of [u8;N] is visited exactly once by IterMut; blanket u8 default is zero; write_volatile overwrites target before compiler_fence(SeqCst). The reference elements recursion retains every returned element, with no discarded restoration continuation. Volatile writes are observable effects in the Rust primitive interpretation and cannot be erased from that interpretation.',
 excludes='No hardware memory fence is asserted. A compiler fence controls compiler ordering. No inspection of emitted deployed machine instructions, registers, spill slots, extra copies, pages after free, persistence, concurrent reads, DMA, or side-channel observations. L3 binary audit remains separate and open.',
 semantics='PV_FXM_ZeroWorld.byte/native/indexed; exact byte overwrite, write/fence counts, outside-target memory preservation, arbitrary frame and allocator/drop counters preserved, caller composition.',
 value='PV_FXM_ZeroSelected.elements/array/scalar; complete Result projected through the exact primitive byte dictionaries. Generic trait effects are not inferred from the name DefaultIsZeroes.',
 drop_caller='Zeroizing<[u8;N]>::drop delegates once to array zeroize; subsequent field glue for the byte array has no user destructor or allocator effect. PV_FXM_ZeroDrop composes this consumed callback with caller state.',
 d188='No Aeneas zeroize iterator emission is credited. Owned index reference keeps each element result; structural gate binds the complete native iterator body. Existing extraction stand-ins are not imported.')
core=(E/'CORE-DEFAULT-SOURCE.rs.txt').read_text()
macro=body(core,'macro_rules! default_impl')
want='{($t:ty, $v:expr, $doc:tt) => {#[stable(feature = "rust1", since = "1.0.0")] #[rustc_const_unstable(feature = "const_default", issue = "143894")] const impl Default for $t {#[inline(always)] #[doc = $doc] fn default() -> $t {$v}}};}'
assert tokens(macro)==tokens(want),macro
invocation=body(core,'default_impl! { u8,')
assert tokens(invocation)==tokens('{u8,0,"Returns the default value of `0`"}'),invocation
j['primitive_default']=dict(source=json.loads((E/'CORE-DEFAULT-SOURCE.json').read_text()),macro=macro,u8_invocation=invocation,complete_tokens_match=True,conclusion='u8 Default returns literal 0 with no world read/write or error path')
(E/'STRUCTURAL-ZEROIZE-GATE.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS complete array/iterator/blanket/volatile/fence bodies')
