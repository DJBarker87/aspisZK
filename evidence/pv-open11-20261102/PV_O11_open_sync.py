"""D573: exact source-branch checks; deliberately no native installation credit."""
from pathlib import Path
import hashlib, json, re, subprocess

D = Path(__file__).parent
sha = lambda b: hashlib.sha256(b).hexdigest()
def tokens(s):
    return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]', re.sub(r'/\*.*?\*/|//[^\n]*', '', s, flags=re.S))
def body(s, anchor):
    a = s.index('{', s.index(anchor)); depth = 0
    for i in range(a, len(s)):
        depth += (s[i] == '{') - (s[i] == '}')
        if depth == 0:
            return s[a:i+1]
    raise ValueError(anchor)
def eq(s, anchor, expected):
    return tokens(body(s, anchor)) == tokens(expected)
def snapshot(path):
    b = subprocess.check_output(['git', 'show', 'ccdc7f48c9:' + path])
    dest = D / 'inputs/io' / (Path(path).name + '.txt')
    dest.write_bytes(b)
    return b.decode()

fs = (D/'inputs/io/fs.rs').read_text()
unix = (D/'inputs/io/fs-unix.rs').read_text()
pal = (D/'inputs/io/pal-unix.rs').read_text()
small = (D/'inputs/io/small_c_string.rs').read_text()
cstring = (D/'inputs/io/c_string.rs').read_text()
fd = (D/'inputs/io/fd-unix.rs').read_text()
owned = (D/'inputs/io/owned-fd.rs').read_text()
error = (D/'inputs/std-error.rs').read_text()
packed = (D/'inputs/std-repr-bitpacked.rs').read_text()
client = (D/'inputs/client/state_only_entropy.rs').read_text()
old = snapshot('evidence/pv-diag12-20261029/PV_DIAG12_Open.lean')
carrier = snapshot('docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_FileCarrier.lean')
typed = snapshot('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_W_TypedEffects.lean')
sync = snapshot('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_W_R_SyncDirectory.lean')

checks = {
 'file_open_read_wrapper': eq(fs, 'pub fn open<P: AsRef<Path>>(path:', '{ OpenOptions::new().read(true).open(path.as_ref()) }'),
 'options_open_wrapper': eq(fs, 'pub fn open<P: AsRef<Path>>(&self, path:', '{ self._open(path.as_ref()) }'),
 'options_inner_wrapper': eq(fs, 'fn _open(&self, path:', '{ fs_imp::File::open(path, &self.0).map(|inner| File { inner }) }'),
 'unix_open_converts_path_first': eq(unix, 'pub fn open(path: &Path, opts:', '{ run_path_with_cstr(path, &|path| File::open_c(path, opts)) }'),
 'open_c_complete': eq(unix, 'pub fn open_c(', '''{
     let flags = libc::O_CLOEXEC | opts.get_access_mode()? | opts.get_creation_mode()?
         | (opts.custom_flags as c_int & !libc::O_ACCMODE);
     let fd = cvt_r(|| unsafe { open64(path.as_ptr(), flags, opts.mode as c_int) })?;
     Ok(File(unsafe { FileDesc::from_raw_fd(fd) })) }'''),
 'access_complete': eq(unix, 'fn get_access_mode(', '''{
     match (self.read, self.write, self.append) {
       (true, false, false) => Ok(libc::O_RDONLY),
       (false, true, false) => Ok(libc::O_WRONLY),
       (true, true, false) => Ok(libc::O_RDWR),
       (false, _, true) => Ok(libc::O_WRONLY | libc::O_APPEND),
       (true, _, true) => Ok(libc::O_RDWR | libc::O_APPEND),
       (false, false, false) => {
         if self.create || self.create_new || self.truncate {
           Err(io::Error::new(io::ErrorKind::InvalidInput,
             "creating or truncating a file requires write or append access",))
         } else {
           Err(io::Error::new(io::ErrorKind::InvalidInput,
             "must specify at least one of read, write, or append access",))
         }
       }
     } }'''),
 'creation_complete': eq(unix, 'fn get_creation_mode(', '''{
     match (self.write, self.append) {
       (true, false) => {}
       (false, false) => {
         if self.truncate || self.create || self.create_new {
           return Err(io::Error::new(io::ErrorKind::InvalidInput,
             "creating or truncating a file requires write or append access",));
         }
       }
       (_, true) => {
         if self.truncate && !self.create_new {
           return Err(io::Error::new(io::ErrorKind::InvalidInput,
             "creating or truncating a file requires write or append access",));
         }
       }
     }
     Ok(match (self.create, self.truncate, self.create_new) {
       (false, false, false) => 0,
       (true, false, false) => libc::O_CREAT,
       (false, true, false) => libc::O_TRUNC,
       (true, true, false) => libc::O_CREAT | libc::O_TRUNC,
       (_, _, true) => libc::O_CREAT | libc::O_EXCL,
     }) }'''),
 'path_encoded_bytes': eq(small, 'pub fn run_path_with_cstr<', '{ run_with_cstr(path.as_os_str().as_encoded_bytes(), f) }'),
 'path_threshold': eq(small, 'pub fn run_with_cstr<', '''{
     if bytes.len() >= MAX_STACK_ALLOCATION { run_with_cstr_allocating(bytes, f) }
     else { unsafe { run_with_cstr_stack(bytes, f) } } }'''),
 'linux_stack_threshold_384': '#[cfg(not(target_os = "espidf"))]\nconst MAX_STACK_ALLOCATION: usize = 384;' in small,
 'stack_path_complete': eq(small, 'unsafe fn run_with_cstr_stack<', '''{
     let mut buf = MaybeUninit::<[u8; MAX_STACK_ALLOCATION]>::uninit();
     let buf_ptr = buf.as_mut_ptr() as *mut u8;
     unsafe {
       ptr::copy_nonoverlapping(bytes.as_ptr(), buf_ptr, bytes.len());
       buf_ptr.add(bytes.len()).write(0);
     }
     match CStr::from_bytes_with_nul(unsafe { slice::from_raw_parts(buf_ptr, bytes.len() + 1) }) {
       Ok(s) => f(s), Err(_) => Err(NUL_ERR),
     } }'''),
 'heap_path_complete': eq(small, 'fn run_with_cstr_allocating<', '''{
     match CString::new(bytes) { Ok(s) => f(&s), Err(_) => Err(NUL_ERR), } }'''),
 'heap_allocates_before_nul_validation': eq(cstring, 'fn spec_new_impl_bytes(', '''{
     let capacity = bytes.len().checked_add(1).unwrap();
     let mut buffer = Vec::with_capacity(capacity);
     buffer.extend(bytes);
     match memchr::memchr(0, bytes) {
       Some(i) => Err(NulError(i, buffer)),
       None => Ok(unsafe { CString::_from_vec_unchecked(buffer) }),
     } }'''),
 'heap_slice_specialization': eq(cstring[cstring.index("impl SpecNewImpl for &'_ [u8]"):], 'fn spec_new_impl(', '{ spec_new_impl_bytes(self) }'),
 'cstring_termination_and_boxing': eq(cstring, 'unsafe fn _from_vec_unchecked(', '''{
     v.reserve_exact(1); v.push(0); Self { inner: v.into_boxed_slice() } }'''),
 'cstring_drop_zero_store': eq(cstring[cstring.index('impl Drop for CString'):], 'fn drop(', '{ unsafe { *self.inner.get_unchecked_mut(0) = 0; } }'),
 'cvt_checks_minus_one_not_any_negative': eq(pal, 'pub fn cvt<T:', '{ if t.is_minus_one() { Err(io::Error::last_os_error()) } else { Ok(t) } }'),
 'cvt_r_complete_unbounded': eq(pal, 'pub fn cvt_r<T,', '''{
     loop { match cvt(f()) { Err(ref e) if e.is_interrupted() => {} other => return other, } } }'''),
 'file_sync_complete': eq(fs, 'pub fn sync_all(', '{ self.inner.fsync() }'),
 'fsync_complete_with_cfg': eq(unix, 'pub fn fsync(', '''{
     cvt_r(|| unsafe { os_fsync(self.as_raw_fd()) })?; return Ok(());
     #[cfg(target_vendor = "apple")] unsafe fn os_fsync(fd: c_int) -> c_int { libc::fcntl(fd, libc::F_FULLFSYNC) }
     #[cfg(not(target_vendor = "apple"))] unsafe fn os_fsync(fd: c_int) -> c_int { libc::fsync(fd) } }'''),
 'fd_wraps_ownedfd': 'pub struct FileDesc(OwnedFd);' in fd and 'pub struct File(FileDesc);' in unix,
 'fd_from_raw': eq(fd[fd.index('impl FromRawFd for FileDesc'):], 'unsafe fn from_raw_fd(', '{ Self(unsafe { FromRawFd::from_raw_fd(raw_fd) }) }'),
 'owned_from_raw_checks_minus_one': eq(owned[owned.index('impl FromRawFd for OwnedFd'):], 'unsafe fn from_raw_fd(', '{ Self { fd: ValidRawFd::new(fd).expect("fd != -1") } }'),
 'owned_drop_single_close_no_retry': eq(owned[owned.index('impl Drop for OwnedFd'):], 'fn drop(', '''{
     unsafe {
       #[cfg(not(target_os = "hermit"))] {
         #[cfg(unix)] crate::sys::fs::debug_assert_fd_is_open(self.fd.as_inner());
         let _ = libc::close(self.fd.as_inner());
       }
       #[cfg(target_os = "hermit")] let _ = hermit_abi::close(self.fd.as_inner());
     } }'''),
 'close_debug_gate_retained': eq(unix, 'pub(crate) fn debug_assert_fd_is_open(', '''{
     use crate::sys::io::errno;
     if core::ub_checks::check_library_ub() {
       if unsafe { libc::fcntl(fd, libc::F_GETFD) } == -1 && errno() == libc::EBADF {
         rtabort!("IO Safety violation: owned file descriptor already closed");
       }
     } }'''),
 'caller_open_then_sync': eq(client[client.index('#[cfg(unix)]\nfn sync_directory'):], 'fn sync_directory(', '{ File::open(directory)?.sync_all() }'),
 'reservation_options_domain': 'options.write(true).create_new(true);\n        #[cfg(unix)]\n        options.mode(0o600);' in client,
 'old_open_has_cut': '| 0,c => ⟨⟨[],.cut⟩,c⟩' in old,
 'old_carrier_does_not_create_authority': 'this subtype does not create OS authority' in carrier,
 'original_typed_algebra_has_three_fields': all(x in typed for x in ['fileOpen : {P : Type}', 'fileSync : std.fs.File', 'optionsOpen : {P : Type}']),
 'original_sync_calls_same_typed_primitives': all(x in sync for x in ['.fileOpen', '.fileSync', 'theorem erase_program']),
 'negative_bounded_retry_rejected': 'fuel' not in body(pal, 'pub fn cvt_r<T,') and 'retry_limit' not in body(pal, 'pub fn cvt_r<T,'),
 'negative_nul_after_options_rejected': 'run_path_with_cstr' in body(unix, 'pub fn open(path: &Path, opts:') and 'get_access_mode' not in body(unix, 'pub fn open(path: &Path, opts:'),
 'error_complete_payload_field': 'error: Box<dyn error::Error + Send + Sync>,' in body(error, 'struct Custom'),
 'error_new_allocates_custom': eq(error, 'fn _new(', '{ Error { repr: Repr::new_custom(Box::new(Custom { kind, error })) } }'),
 'error_os_captures_errno': eq(error, 'pub fn last_os_error(', '{ Error::from_raw_os_error(sys::io::errno()) }'),
 'error_owned_conversion_prevents_double_drop': eq(packed, 'pub(super) fn into_data(', '{ let this = core::mem::ManuallyDrop::new(self); unsafe { decode_repr(this.0, |p| Box::from_raw(p)) } }'),
 'error_drop_reconstructs_custom_owner': eq(packed[packed.index('impl Drop for Repr'):], 'fn drop(', '{ unsafe { let _ = decode_repr(self.0, |p| Box::<Custom>::from_raw(p)); } }'),
}
rows = {
 'V171': {'status': 'OPEN', 'rank': 6, 'exact_premise':
   'Instantiate the SAME op14/fileOpen typed algebra on the native caller, not a pure world lift. Bind generic P::as_ref and P destruction; new/read-only options; Unix path bytes, stack/heap conversion at 384, allocation-before-NUL-validation, NUL Error and CString zero-store/deallocation; ordered flag validation, open64/errno and unbounded Interrupted retry; fd adoption and complete returned Result with its post-world. Preserve native ownership, cleanup/abort prefixes and the existing sync_directory caller/observer. DIAG12 openRetry is a finite prefix, not completion/divergence. No new success assumption or T field.'},
 'V175': {'status': 'OPEN', 'rank': 7, 'exact_premise':
   'Instantiate the SAME op22/optionsOpen on actual Options and P in the full native world. Path conversion occurs BEFORE access/creation validation. Bind all flag/mode bits (custom i32 masks ACCMODE only), validation Error::new payload/allocation and abort, open64 pointer/mode ABI, errno capture, unbounded EINTR retries, successful FileDesc ownership and all argument/temporary drops. The actual reservation domain is write/create_new/custom0/mode0600, but every other reached caller needs an exclusion or the general branch law. Preserve complete Result/error/world/observer and no fuel bound. Source validation checks alone do not install this link.'},
 'V172': {'status': 'OPEN', 'rank': 8, 'exact_premise':
   'Instantiate the SAME op15/fileSync typed algebra for the actual borrowed fd and native pre/post-world. Bind fsync (Linux, not Apple F_FULLFSYNC), cvt of -1, immediate errno/Error capture, unbounded Interrupted retry, other errors and successful unit return, with the owner preserved during the borrow. The surrounding caller closes the directory File on ordinary return, and the reservation File after its later directory-sync prefix or ordinary error; panic=abort does not unwind. Retain per-attempt resources, failures, blocking/divergence and ordered native observation. No success/fuel premise or new T field.'},
 'V268': {'status': 'OPEN', 'rank': 9, 'exact_premise':
   'Supply the SAME ExternalTypes.op3 native interpretation for all four Error representations, preserving OS code, valid Simple discriminant, static SimpleMessage and entire Custom {kind, Box<dyn Error+Send+Sync>} with its allocation/payload/vtable ownership. Bind constructors, moves, into_data ManuallyDrop, decoding, shared/mutable access, observations and Custom destruction/deallocation exactly once, in the actual world and caller frame. Error::new allocation/abort and errno-based construction remain included. The borrowed reference and a Kind-only quotient do not supply this ownership/type law; no getter reattempt is made. V176 remains the separately recorded pure getter obligation, and neither row is discharged by assigning its missing work to the other. Dynamic payload/drop/formatting associations and reached domains remain explicit.'},
 'V271': {'status': 'OPEN', 'rank': 10, 'exact_premise':
   'Bind std File -> sys File -> FileDesc -> OwnedFd/ValidRawFd to the existing nonnegative I32 value view with a live ownership invariant in the SAME world. A subtype or descriptor roundtrip supplies no live fd authority. Prove successful open transfers the returned live fd once; borrowed I/O never duplicates/releases it; each ordinary scope exit destroys the owner once. Linux Drop issues one close, ignores its result and does NOT retry EINTR. Bind the check_library_ub/debug fcntl/abort gate at the adopted configuration, fd reuse/provenance and all native returned/post-world observations. Abort paths retain their actually performed prefixes without invented stack cleanup. No availability or exactly-once physical-close success assumed.'},
}
report = dict(classification='script-checked source branches and exact existing consumer census; NOT own-1 complete structural binding, native installation, release audit or restored rows',
    revision='ccdc7f48c9', checks=checks, ok=all(checks.values()), rows=rows,
    attempts={r: {'source_inspection_passes': 1, 'lean': 0, 'native': 0} for r in rows},
    next_rank=11, next_row='V239', restored=0,
    source_bodies={name: body(src, anchor) for name, src, anchor in [
      ('open_c', unix, 'pub fn open_c('), ('cvt_r', pal, 'pub fn cvt_r<T,'),
      ('fsync', unix, 'pub fn fsync('), ('long_path', cstring, 'fn spec_new_impl_bytes(')]},
    inputs={str(p.relative_to(D)): sha(p.read_bytes()) for p in list((D/'inputs/io').glob('*')) + [D/'inputs/std-error.rs', D/'inputs/std-repr-bitpacked.rs'] if p.is_file()},
    retained=['V370 compiler/runtime preservation', 'V268 native Error/value and payload ownership', 'E1/E2', 'full native joint observer', 'coherent dependent replay'],
    premises_removed=0, premises_added=0, premises_weakened=0)
(D/'PV_O11_open-sync.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({'ok': report['ok'], 'checks': len(checks), 'failed': [k for k,v in checks.items() if not v], 'restored': 0}))
assert report['ok']
