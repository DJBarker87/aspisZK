"""Exact deployed uint bodies plus selected macro instantiations.
Intrinsic meaning is retained compiler/tool trust; no LLVM theorem is claimed.
"""
from pathlib import Path
import runpy,json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
a=runpy.run_path(str(D/'range-source.py'))
span,tokens,root,sha=a['span'],a['tokens'],a['root'],a['sha']
checks=[]
for op,law in [('add','add32_binding/add64_binding'),('sub','sub32_binding'),('mul','mul64_binding')]:
 name='wrapping_'+op
 expected=f'pub const fn {name}(self, rhs: Self) -> Self {{ intrinsics::{name}(self, rhs) }}'
 checks.append((name,expected,'R1Z.PV_RDCD3_Word194.'+law))
checks += [
 ('wrapping_shr','''pub const fn wrapping_shr(self, rhs: u32) -> Self {
  unsafe { self.unchecked_shr(rhs & (Self::BITS - 1)) }
 }''','R1Z.PV_RDCD3_Word194.shr16_binding/shr64_binding/unchecked16_bound/unchecked64_bound'),
 ('unchecked_shr','''pub const unsafe fn unchecked_shr(self, rhs: u32) -> Self {
  assert_unsafe_precondition!(check_language_ub,
   concat!(stringify!($SelfT), "::unchecked_shr cannot overflow"),
   (rhs: u32 = rhs,) => rhs < <$ActualT>::BITS,);
  unsafe { intrinsics::unchecked_shr(self, rhs) }
 }''','R1Z.PV_RDCD3_Word194.unchecked16_bound/unchecked64_bound/boundedShr'),
 ('unchecked_add','''pub const unsafe fn unchecked_add(self, rhs: Self) -> Self {
  assert_unsafe_precondition!(check_language_ub,
   concat!(stringify!($SelfT), "::unchecked_add cannot overflow"),
   (lhs: $SelfT = self, rhs: $SelfT = rhs,) => !lhs.overflowing_add(rhs).1,);
  unsafe { intrinsics::unchecked_add(self, rhs) }
 }''','R1Z.PV_RDCD3_Range194.successor_bound/extracted/projection; concrete reached increment is one')]
p=root/'num/uint_macros.rs';s=p.read_text();out=[]
for name,expected,law in checks:
 marker='pub const '+('unsafe ' if name.startswith('unchecked') else '')+'fn '+name+'('
 actual=span(s,'macro_rules! uint_impl',marker)
 assert tokens(actual)==tokens(expected),(name,actual)
 # Semantic mutations, rather than harness-name changes.
 bad=expected.replace('intrinsics::'+name,'intrinsics::changed_'+name,1) if 'intrinsics::'+name in expected else expected.replace('rhs &','rhs |',1)
 assert tokens(actual)!=tokens(bad),name
 out.append(dict(method=name,body=actual,expected_body=expected,law=law,token_sha256=sha('\0'.join(tokens(actual)).encode()),negative_control='changed intrinsic/mask rejected'))
pmod=root/'num/mod.rs';mod=pmod.read_text();bindings=[]
for ty,actual,bits in [('u16','u16',16),('u32','u32',32),('u64','u64',64),('usize','u64',64)]:
 context='impl '+ty+' {' if ty!='usize' else '#[cfg(target_pointer_width = "64")]\nimpl usize {'
 body=span(mod,context,'uint_impl!')
 for text in [f'Self = {ty}',f'ActualT = {actual}',f'BITS = {bits}',f'BITS_MINUS_ONE = {bits-1}']:
  assert tokens(text) in [tokens(body)[i:i+len(tokens(text))] for i in range(len(tokens(body)))],(ty,text)
 bindings.append(dict(type=ty,actual_type=actual,bits=bits,cfg='target_pointer_width=64' if ty=='usize' else 'unconditional',macro_invocation=body))
assert 'pub const BITS: u32 = Self::MAX.count_ones();' in s
result=dict(toolchain='1.94.1',uint_macro_file=dict(path=str(p),sha256=sha(p.read_bytes())),num_file=dict(path=str(pmod),sha256=sha(pmod.read_bytes())),methods=out,bindings=bindings,bits_definition='Self::MAX.count_ones(); integer intrinsic boundary retained',scope='Six exact uint method bodies and four concrete macro bindings; not a complete row checker',composition_trust='Reclassification within existing compiler/Aeneas tool trust; zero endpoint premise removal')
(D/'v260-word-source-result.json').write_text(json.dumps(result,indent=2)+'\n')
print('Six complete uint bodies, six rejecting semantic controls, and u16/u32/u64/64-bit-usize macro bindings matched')
