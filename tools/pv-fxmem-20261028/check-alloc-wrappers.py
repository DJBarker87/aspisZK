"""Check the thin Global/runtime bindings; no compiler is launched."""
from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028'
src=(R/'tools/pv-fxmem-20261028/structural-drop.py').read_text();exec(src[src.index('def clean('):src.index('expected=')])
j=json.loads((E/'ALLOC-WRAPPERS.json').read_text())
expected={
'fn allocate(&self, layout: Layout)':'{self.alloc_impl(layout,false)}',
'unsafe fn grow(':'{unsafe {self.grow_impl(ptr,old_layout,new_layout,false)}}',
'const fn alloc_impl(':'{core::intrinsics::const_eval_select((layout,zeroed),Global::alloc_impl_const,Global::alloc_impl_runtime,)}',
'const unsafe fn grow_impl(':'{core::intrinsics::const_eval_select((self,ptr,old_layout,new_layout,zeroed),Global::grow_shrink_impl_const,Global::grow_impl_runtime,)}',
'pub unsafe fn dealloc(':'{unsafe {dealloc_nonnull(NonNull::new_unchecked(ptr),layout)}}',
'unsafe fn dealloc_nonnull(':'{unsafe {__rust_dealloc(ptr,layout.size(),layout.alignment())}}'}
assert len(j['bodies'])==len(expected)
for x in j['bodies']:
 assert tokens(x['body'])==tokens(expected[x['anchor']]),x
 x['complete_tokens_match']=True
for name in ['STRUCTURAL-DROP-GATE.json','STRUCTURAL-RESERVE-GATE.json']:
 p=E/name;gate=json.loads(p.read_text())
 expected_sha=gate['files']['alloc']['sha256'] if 'files' in gate else next(x['file_sha256'] for x in gate['checks'] if x['file']==j['path'])
 assert j['sha256']==expected_sha
 gate['thin_allocator_wrappers']=j
 gate['wrapper_binding']='Global allocate/grow pass zeroed=false and runtime const_eval_select selects the runtime bodies in this non-const call. The dealloc reference wraps the same valid nonnull pointer and forwards the same Layout to dealloc_nonnull. Pointer wrapping/unwrapping is representation identity on valid owned allocations; both sides reach the identical deallocation primitive. No generic invalid-pointer or const-execution law is claimed.'
 p.write_text(json.dumps(gate,indent=2)+'\n')
print('PASS 6 complete thin Global/alloc/dealloc wrapper bodies and matching pinned file hashes')
