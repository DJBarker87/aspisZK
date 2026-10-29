from pathlib import Path
import json,lzma,hashlib,re
D=Path('evidence/pv-b3q-20261029');B=Path('evidence/pv-b3p6-20261028');x=json.load(lzma.open(B/'std227-stdcone-resume5.json.xz','rt'));f=x['files']['core/src/array/equality.rs']['deployed'];s=f['text'];anchor='impl<T: [const] BytewiseEq<U>, U, const N: usize> const SpecArrayEq<U, N> for T';body=s[s.index(anchor):];assert 'unsafe { crate::intrinsics::raw_eq(a, crate::mem::transmute(b)) }'in body;assert '!Self::spec_eq(a, b)'in body
llvm=json.loads((B/'resume7/llvm227-trace-resume7.json').read_text());calls=[]
def visit(v):
 if isinstance(v,dict):
  if v.get('callee')=='bcmp' and 'i64 32' in v.get('text',''):calls.append(v)
  for a in v.values():visit(a)
 elif isinstance(v,list):
  for a in v:visit(a)
visit(llvm);assert len(calls)==2,calls
native=Path('tools/pv-b3p6-20261028/v244/host_terminal.rs').read_text();assert 'source.pool != public.pool'in native and 'source.deployment_domain != public.deployment_domain'in native
out=dict(status='source specialization resolved; value/source binding requires compiled specialized_link; native runtime and compiler boundary separate',source_file=f['path'],source_file_sha256=f['sha256'],specialized_impl=body,specialized_impl_sha256=hashlib.sha256(body.encode()).hexdigest(),native_call_sites=['validate_transition: source.pool != public.pool','validate_transition: source.deployment_domain != public.deployment_domain'],carrier='[u8;32] on both sides; BytewiseEq<u8> for u8; transmute is identity on identical reference types',supporting_llvm=calls,steps=['eq: shared references retained','cast right reference to the same [u8;32] reference type: identity; transmute intrinsic remains V370','raw_eq compares all 32 initialized bytes; no array padding','ne: call spec_eq once, negate Bool result','no store/drop/allocator/formatting/error/abort in either source wrapper'],compiler_boundary=['V370 / D381,D386','core::intrinsics::raw_eq','core::mem::transmute','runtime bcmp'],old_generic_row_is_not_a_binding_for_this_specialization=True,no_trust_field_added=True)
(D/'byte-array-specialization.json').write_text(json.dumps(out,indent=2)+'\n')
