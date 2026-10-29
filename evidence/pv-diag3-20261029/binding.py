"""Statement-order checks for the deployed source regions, not a proof that
opaque operations have the model's executions. Open influence channels stay P.
"""
from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag3-20261029')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows={r['name']:r for r in json.loads((D/'source-regions.json').read_text())}
specs=[
('write_all',['while !buf.is_empty()','match self.write(buf)','Ok(0)','Error::WRITE_ALL_EOF','Ok(n) => buf = &buf[n..]','e.is_interrupted()','Err(e) => return Err(e)','Ok(())'],
 'writeAllStep / writePrefix',
 ['while empty test→pure Ok; each write→write op','Ok0→zeroError; Okn→checked drop n and source slicePanic','Err ref Interrupted→guard, full error destruction, same buf continuation','Err noninterrupted→move error; completed buffer→Ok'],
 ['interruptedGuard includes abnormal owned-error cleanup','slice bounds and concrete bytes/usize representation','loop suffix must be actual native suffix, not artificial fuel divergence']),
('default_write_fmt',['struct Adapter','inner:','error: Result<()>','fn write_str','self.inner.write_all','self.error = Err(e)','Err(fmt::Error)','let mut output','fmt::write','output.error.is_err()','output.error','panic!'],
 'adapterWrite / defaultFmt',
 ['Adapter.error initially Ok; initialization/store effects belong to format op','write_str Ok returns fmt Ok; Err replaces slot before fmt Err','replacement includes old-slot Drop and RHS cleanup if Drop unwinds','fmt Ok drops remaining slot; fmt Err moves stored I/O error or panics on empty slot'],
 ['fmt::write and formatter callback bodies with actual mutable Adapter state','replaceError/dropSlot complete glue, memory validity and borrow restoration','panic/hook/abort concrete executions']),
('write_fmt',['as_statically_known_str','write_all(s.as_bytes())','default_write_fmt'],
 'writeFmt',['known literal fast path; dynamic default formatter path'],['Arguments representation and byte conversion laws']),
('unix_fd_write',['let ret = cvt','libc::write','self.as_raw_fd()','buf.as_ptr()','cmp::min(buf.len(), READ_LIMIT)','Ok(ret as usize)'],
 'fdWrite / cvtWrite',['fd, supplied buffer and min count→syscall','cvt minus-one→lastError before returning Err','success preserves actual ret-as-usize'],
 ['libc write partial delivery, errno read and source Error representation','castUsize is the deployed 64-bit cast, not toNat of negative values','actual readLimit and OS permitted return ranges']),
('unix_stdio',['impl Stderr','Stderr','impl io::Write for Stderr','ManuallyDrop::new(FileDesc::from_raw_fd(STDERR_FILENO)).write(buf)','fn flush','Ok(())'],
 'rawStderrWrite',['fixed fd2; ManuallyDrop prevents accidental close of borrowed descriptor','flush leaf returns Ok, no write'],['raw-vectored path and global Stderr reentrant lock/RefCell/TLS layers remain open']),
('backtrace_create_status',['let _lock = lock()','let mut frames = Vec::new()','let mut actual_start = None','set_image_base()','trace_unsynchronized','frames.push','frame.clone()','frame.symbol_address().addr() == ip && actual_start.is_none()','actual_start = Some(frames.len())','frames.is_empty()','Inner::Unsupported','Inner::Captured(LazyLock::new(lazy_resolve(Capture','actual_start.unwrap_or(0)','pub fn status'],
 'createTrace / pushFrame / finishCapture / traceStatus',
 ['lock; empty Vec/None initialization; image base; complete unwinder trace op','callback pushes cloned raw frame with empty symbols before first-match selection','no frames→Unsupported; otherwise lazy owned Capture with default start0','scope releases lock on return/unwind, not abort/divergence','status only discriminant, no symbolization'],
 ['trace op must refine every actual frame clone/push, allocation and cleanup','frame addresses, image-base, unwind stack and lock scheduling public-law obligation','package includes LazyLock construction/ownership transfer and failure cleanup']),
('lazy_drop',['match self.once.state()','OnceExclusiveState::Incomplete','ManuallyDrop::drop(&mut self.data.get_mut().f)','OnceExclusiveState::Complete','ManuallyDrop::drop(&mut self.data.get_mut().value)','OnceExclusiveState::Poisoned'],
 'lazyDrop',['Incomplete drops closure; Complete drops value; Poisoned drops neither','drop does not call the resolver closure'],['source Once state→LazyState and union ownership representation','closure/value field destructors including vectors/backtrace symbols']),
('box_drop',['let ptr = self.0','Layout::for_value_raw','if layout.size() != 0','self.1.deallocate'],
 'boxDeallocate / allocationDrop',['pointee drop precedes Box::drop (explicit source comment)','layout size0 skips deallocate; nonzero layout→allocator op','pointee unwind still runs allocation cleanup; abort/divergence do not'],['valid layout/pointer and compiler-generated drop glue at V370','allocator size/order/address/state influence laws remain rdea-1/P']),
('vec_drop',['ptr::drop_in_place','self.as_mut_ptr()','self.len','RawVec handles deallocation'],
 'allocationDrop',['drop vector elements before RawVec field deallocation','remaining-element cleanup on element panic is still an explicit payload-drop leaf'],['full slice drop glue/element destructor executions and RawVec layout']),
('rawvec_drop',['self.inner.deallocate(T::LAYOUT)'],
 'allocationDrop',['RawVec drops backing allocation, not elements a second time'],['RawVecInner::deallocate layout/capacity and allocator influence']),
('anyhow_drop',['impl Drop for Error','vtable(self.inner.ptr).object_drop','unsafe fn object_drop<E>','e.cast::<ErrorImpl<E>>()','drop(unsafe { unerased_own.boxed() })'],
 'errorObjectDrop / allocationDrop',['read vtable; call selected concrete object_drop','recover exact ErrorImpl<E> Box then complete Box/pointee destruction','fields vtable ref, backtrace, _object in declared source order; then allocation'],['vtable/layout/pointer memory laws, exact E selected by constructor','all message/backtrace field destructor and allocator executions']),
]
result=[]
for name,needles,model,steps,remaining in specs:
 r=rows[name];body=r['text'];last=-1
 for needle in needles:
  k=body.find(needle,last+1);assert k>=0,(name,needle);last=k
 result.append(dict(source=r,ordered_checks=needles,model=model,steps=steps,open_native_obligations=remaining))
for r in rows.values():assert sha(Path(r['path']))==r['file_sha256']
# Deployed dependency features/profile are inherited, never rebuilt/defaulted.
U=D.parent/'codex-pv-diag-20261029/resolved-build-units.json'
units=json.loads(U.read_text())
model_pins={p.stem:sha(p) for p in (D/'sources').glob('PV_DIAG3_*.lean')}
record=dict(classification='partial statement-level deployed-source bindings under own-1, with complete region text; no full native leaf closure claimed',bindings=result,all_regions=rows,models=model_pins,resolved_build_units_sha256=sha(U),resolved_build_units=units,deployed_rustc='1.94.1',compiler_boundary='V370 / owner D381/D386 retained',restored_class_B_rows=[],
 influence_classification=dict(memory_primitives='caller-supplied memory permitted at V370, no additional information source',allocator='success/failure rdea-1; returned addresses; later-read state writes all retained obligations',write='syscall, fd state, partial writes and errno disqualify input-free treatment',capture='environment/cache/locks/unwinder/image/module state and PCs disqualify input-free treatment',drop='input-owned layouts/vtables/fields and allocator effects require own-1; LazyLock drop does not resolve symbols',evidence='native controls are finite validation; no singleton-input-domain claim'),
 whole_run_public_law=False,new_trust_fields=0)
(D/'binding.json').write_text(json.dumps(record,indent=2)+'\n');print('bound source regions',len(result),'all unresolved native leaves named; no restored row')
