"""Structural own-1 binding for the selected deployed getrandom driver.
No native execution, extractor changes, compiler claim, or extra trust field.
"""
from pathlib import Path
import json,hashlib,subprocess,sys
E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=json.load(open(E/'getrandom-034-linux-raw-source.json'))
s={x['relative']:x['text'] for x in rows}
for x in rows:assert sha(x['text'].encode())==x['sha256']
client=json.load(open(E/'native-sources.json'))['client']
recipe=next(x for x in client if x['path'].endswith('build-client.sh'))
assert '--cfg getrandom_backend="linux_raw"' in recipe['text']
lock=subprocess.check_output(['git','show','HEAD:tools/r1-cost-probe/Cargo.lock'],text=True)
assert 'name = "getrandom"\nversion = "0.3.4"' in lock
raw=s['src/backends/linux_raw.rs']
a=raw.index('pub fn fill_inner(')
body=raw[a:]
expected='''pub fn fill_inner(mut dest: &mut [MaybeUninit<u8>]) -> Result<(), Error> {
    // Value of this error code is stable across all target arches.
    const EINTR: isize = -4;

    loop {
        let ret = unsafe { getrandom_syscall(dest.as_mut_ptr().cast(), dest.len(), 0) };
        unsafe { sanitizer::unpoison_linux_getrandom_result(dest, ret) };
        match usize::try_from(ret) {
            Ok(0) => return Err(Error::UNEXPECTED),
            Ok(len) => {
                dest = dest.get_mut(len..).ok_or(Error::UNEXPECTED)?;
                if dest.is_empty() {
                    return Ok(());
                }
            }
            Err(_) if ret == EINTR => continue,
            Err(_) => {
                let code = i32::try_from(ret).map_err(|_| Error::UNEXPECTED)?;
                return Err(Error::from_neg_error_code(code));
            }
        }
    }
}
'''
assert body==expected,'complete raw driver changed'
steps=[
 ('const EINTR: isize = -4;','loop ret = -4; interrupted'),
 ('getrandom_syscall(dest.as_mut_ptr().cast(), dest.len(), 0)','syscall (address+offset) (64-offset); raw ABI flags=0'),
 ('sanitizer::unpoison_linux_getrandom_result(dest, ret)','non-MSAN unpoison is no-op, bounds checks do not panic'),
 ('match usize::try_from(ret)','loop checks nonnegative signed64 raw return; nonnegative fits usize64'),
 ('Ok(0) => return Err(Error::UNEXPECTED)','zero; retains raw post-buffer'),
 ('dest = dest.get_mut(len..).ok_or(Error::UNEXPECTED)?','oversized; otherwise short_read advances offset with entire original buffer retained'),
 ('if dest.is_empty()','complete; offset+length=64'),
 ('Err(_) if ret == EINTR => continue','interrupted; same offset, post-buffer/world/events passed to next call'),
 ('i32::try_from(ret).map_err(|_| Error::UNEXPECTED)?','negative_overflow; lower bound signed32, upper bound automatic from negativity'),
 ('return Err(Error::from_neg_error_code(code))','negative; preserves negative OS error without libc errno read or write')]
for text,law in steps:assert text in body
# Complete target branch: preserve syscall clobbers as compiler/ABI P, no libc call.
x=raw[raw.index('} else if #[cfg(target_arch = "x86_64")]'):raw.index('} else {\n            compile_error!')]
for t in ['OFFSET + 318','in("rdi") buf','in("rsi") buflen','in("rdx") flags','lateout("rax") r0','lateout("rcx") _','lateout("r11") _','options(nostack, preserves_flags)']:assert t in x
assert 'getrandom_msan' in s['build.rs'] and 'if #[cfg(getrandom_msan)]' in s['src/backends/sanitizer.rs']
assert 'let _ = buf;' in s['src/backends/sanitizer.rs']
assert 'getrandom_backend = "linux_raw"' in s['src/backends.rs']
for t in ['INTERNAL_START: RawOsError = 1 << 16','UNEXPECTED: Error = Self::new_internal(2)','if code < 0','Self(code)']:assert t in s['src/error.rs']
for mod in ['LinuxRawControl','LinuxRawBranches','LinuxRawObserve','LinuxRawCodes','EntropySourceSlot','NativeRawSelection','NativeLinuxError','NativeRawError']:
 text=Path('lean/PV_EVH_'+mod+'.lean').read_text();assert 'sorry' not in text
out=dict(evidence_class='structural argument (own-1), deployed dependency body to source control model',
 recipe=recipe,lockfile_sha256=sha(lock.encode()),dependency='getrandom0.3.4',
 target='adopted D474(C) Linux x86_64, pointer_width64, backend linux_raw, no MSAN',
 complete_source_sha256=next(x['sha256'] for x in rows if x['relative']=='src/backends/linux_raw.rs'),
 complete_fill_inner=body,steps=[dict(source=a,model=b) for a,b in steps],
 observation='LinuxRawObserve replaces LinuxRawSyscall; syscall response carries return metadata only, buffer remains in physical/mutable state; L3 joint observation remains P',
 runtime_frame='No allocation, deallocation, handles or libc errno calls in fill/fill_uninit/fill_inner/raw syscall source cone. Model updates only output buffer and OS world.',
 source_buffer='Only the reached fresh zero-initialized64 array. Driver is not an arbitrary-length getrandom law.',
 reached_installation='NativeRawSelection.error_fill installs op129 at opsNative for the current primitive delivery. NativeRawError.error_connected joins the actual extracted error iteration, deployed zeroize1.9.0 cleanup, heap/live invariants and retained events; no uniform advancing-world dictionary view.',
 admission='EntropySourceSlot proves initialized64 extent and fresh ghost identity from all live/retired lifetimes. Physical address is an input, never synthesized; heap/live address separation remains P.',
 trust_boundary='entropy_kernel remains the existing JOINT DENSITY field only. Raw syscall ABI, memory footprint, source-frame validity and full native/extracted simulation remain P; no missing proof is added to or folded into T.',
 retained=['complete source/carrier association; all_codes proves reached nonzero i32 representation','complete provenance-fixed residual family; local reached-world op129 installation alone is not full-entry installation','raw syscall ABI, kernel memory footprint and intermediate memory/L3 history remain P; not a consequence of entropy_kernel density','non-MSAN deployed artifact/config provenance','original source stack key/address provenance','full entropy success/retry and entry','L3 joint observation and V370'],
 trust_fields_added=[],rows_removed=[])
p=E/'getrandom-linux-raw-binding.json'
if '--check' in sys.argv:assert json.load(open(p))==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS complete linux_raw control binding; actual kernel/frame/entry obligations retained')
