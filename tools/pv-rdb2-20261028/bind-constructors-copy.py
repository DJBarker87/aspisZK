"""Exact 1.94.1 constructors and reached copy implementation for V238.
The existing complete Ct wrapper binding is reused unchanged; this adds the
previously missing std-body/effect associations, rather than retesting it.
"""
from pathlib import Path
import json,re,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028')
L=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'"(?:[^"\\]|\\.)*"|::|=>|\w+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  d+=(s[i]=='{')-(s[i]=='}')
  if not d:return s[a:i+1]
 raise ValueError(needle)
checks=[]
def check(rel,needle,expected,law):
 p=L/rel;raw=p.read_bytes();b=body(raw.decode(),needle);assert tokens(b)==tokens(expected),(rel,needle,b)
 checks.append(dict(path=str(p),file_sha256=hashlib.sha256(raw).hexdigest(),item=needle,body=b,exact_tokens=True,law=law))
nn='core/src/ptr/non_null.rs'
check(nn,'pub const fn from_mut(', '{unsafe{NonNull{pointer:r as *mut T}}}', 'ConstructorEffects.from_mut_complete')
check(nn,'pub const unsafe fn new_unchecked(', '''{unsafe{
 assert_unsafe_precondition!(check_language_ub,"NonNull::new_unchecked requires that the pointer is non-null",
 (ptr:*mut ()=ptr as *mut ())=>!ptr.is_null());NonNull{pointer:ptr as _}}}''',
 'ConstructorEffects.new_unchecked_complete; nonzero supplied by valid reference/slice representation')
check(nn,'pub const fn without_provenance(', '{let pointer=crate::ptr::without_provenance(addr.get());unsafe{NonNull{pointer}}}',
 'ConstructorEffects.without_provenance_complete; no permission to read or new allocation inferred')
check(nn,'pub const fn slice_from_raw_parts(', '{unsafe{Self::new_unchecked(super::slice_from_raw_parts_mut(data.as_ptr(),len))}}',
 'ConstructorEffects.slice_complete/slice_nonzero/slice_provenance')
check('core/src/ptr/mod.rs','pub const fn without_provenance<T>', '{without_provenance_mut(addr)}', 'explicit no-provenance constructor')
check('core/src/ptr/mod.rs','pub const fn without_provenance_mut<T>', '{unsafe{mem::transmute(addr)}}',
 'sysroot integer-to-pointer intrinsic representation; ConstructorEffects.without_provenance_complete; never dereferenced')
check('core/src/ptr/mod.rs','pub const fn slice_from_raw_parts_mut<T>', '{from_raw_parts_mut(data,len)}',
 'ConstructorEffects.slice_complete: data/provenance unchanged, length becomes metadata')
check('core/src/slice/mod.rs','pub const fn copy_from_slice(', '{unsafe{copy_from_slice_impl(self,src)}}', 'CopyEffects.copy_complete/copy_rejected')
p=L/'core/src/slice/mod.rs';raw=p.read_bytes();whole=body(raw.decode(),'const unsafe fn copy_from_slice_impl<')
tail=whole[whole.index('if dest.len()'):]
assert tokens(tail)==tokens('''if dest.len()!=src.len(){len_mismatch_fail(dest.len(),src.len());}
 unsafe{ptr::copy_nonoverlapping(src.as_ptr(),dest.as_mut_ptr(),dest.len());}}''')
assert 'const fn len_mismatch_fail(dst_len: usize, src_len: usize) -> !' in whole
assert 'const_panic!' in whole
checks.append(dict(path=str(p),file_sha256=hashlib.sha256(raw).hexdigest(),item='copy_from_slice_impl',body=whole,
 runtime_main_body_tokens_equal=True,length_error='const_panic -> Aeneas panic error; no copy on mismatch',
 law='CopyEffects.copy_complete/copy_rejected/source_preserved/copy_frame; CtCopy.copy_complete/returned_length/complete_frame'))
proofs={
 'constructors':'R1Z.PV_RDB2_ConstructorEffects.*',
 'default32':'CopyEffects.initialized32 and PV_DL_CtCarrier.initial_byte; native GenericArray generation/default dependency body unchanged',
 'copy':'CtCopy.copy_complete/returned_length/complete_frame',
 'result':'PV_DL_CtCarrier.complete; PV_DL_CtSelected.selected_native in the owned import-narrowed cohort'}
(D/'V238-deployed-body-binding.json').write_text(json.dumps(dict(row='V238',checks=checks,proofs=proofs,
 profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',toolchain='rustc1.94.1',
 resolved_features_reference='native-ct/receipt.json',
 original_wrapper_binding='wrapper-structural/results.json, already PASS on deployed dependencies; inputs unchanged',
 side_and_size='Both original truncation sides; full32 and native output shape<=32; no guard weakened',
 effect_boundary='original variable-finalizer and TRUNC_SIDE complete Results remain explicit parameters; all returned core/buffer/output preserved; source/output borrowing is disjoint',
 excluded_envelope='AtomicPtr, CStr and formatting bodies occur outside the admitted wrapper/default/copy boundary or inside explicit callback parameters; not associated as reached copy bodies',
 machine_boundary='Rust memory/intrinsic and compiler correspondence retained at the original structural-route boundary; no new T field; V232 unchanged',restored=False),indent=2)+'\n')
print('PASS exact deployed NonNull constructors, pointer metadata construction, slice-copy guard and copy call')
