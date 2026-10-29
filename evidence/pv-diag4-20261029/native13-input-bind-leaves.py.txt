from pathlib import Path
import json,hashlib,re,subprocess,tomllib,tarfile
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Exact balanced Rust body extraction, ignoring braces in comments/strings.
token=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\{|\}|[^{}"/]+|.',re.S)
def region(path,marker,start=0):
 text=path.read_text();at=text.index(marker,start);body=text.index('{',at);depth=0
 for m in token.finditer(text,body):
  if m.group()=='{':depth+=1
  if m.group()=='}':
   depth-=1
   if depth==0:return dict(path=str(path),file_sha256=sha(path),start_line=text[:at].count('\n')+1,text=text[at:m.end()])
 raise ValueError(marker)
def norm(s):return re.sub(r'\s+','',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
b=[]
def add(name,path,marker,expect,model,steps,open_=[] ,start=0):
 r=region(R/path,marker,start);assert norm(r['text'])==norm(expect),(name,r['text']);b.append(dict(name=name,source=r,model=model,steps=steps,open_native_obligations=open_))
add('status','std/src/backtrace.rs','pub fn status(&self)', '''pub fn status(&self) -> BacktraceStatus {
match self.inner { Inner::Unsupported => BacktraceStatus::Unsupported,
Inner::Disabled => BacktraceStatus::Disabled,
Inner::Captured(_) => BacktraceStatus::Captured, }}''','PV_DIAG4.status',
 ['borrow self; read discriminant','three branches return corresponding enum','captured payload borrowed, neither forced nor moved','no stores, calls, allocations, destructor or panic branches'],['borrowed memory representation/source-to-machine preservation V370'])
p=R/'std/src/sys/stdio/unix.rs';t=p.read_text();start=t.index('impl io::Write for Stderr')
add('raw_flush','std/src/sys/stdio/unix.rs','fn flush(&mut self)', 'fn flush(&mut self) -> io::Result<()> { Ok(()) }','PV_DIAG4.rawFlush',['construct Ok unit; return; no calls, stores or drop payload'],['V370'],start=start)
add('raw_vectored','std/src/sys/stdio/unix.rs','fn is_write_vectored(&self)', 'fn is_write_vectored(&self) -> bool { true }','PV_DIAG4.rawIsWriteVectored',['return true'],['V370'],start=start)
add('raw_new','std/src/sys/stdio/unix.rs','pub const fn new()', 'pub const fn new() -> Stderr { Stderr }','PV_DIAG4.rawStderrNew',['construct zero-field Stderr; return'],['V370'],start=t.index('impl Stderr'))
add('panic_output','std/src/sys/stdio/unix.rs','pub fn panic_output()', 'pub fn panic_output() -> Option<impl io::Write> { Some(Stderr::new()) }','PV_DIAG4.panicOutput',['call concrete rawStderrNew law','construct Some; return'],['V370'])
add('once_wrapper','std/src/sync/once.rs','pub(crate) fn state(&mut self)', 'pub(crate) fn state(&mut self) -> OnceExclusiveState { self.inner.state() }','PV_DIAG4.onceState',['exclusive self.inner; call futex state law'],['exclusive native representation/V370'])
add('once_state','std/src/sys/sync/once/futex.rs','pub(crate) fn state(&mut self)', '''pub(crate) fn state(&mut self) -> OnceExclusiveState { match *self.state_and_queued.get_mut() {
INCOMPLETE => OnceExclusiveState::Incomplete, POISONED => OnceExclusiveState::Poisoned,
COMPLETE => OnceExclusiveState::Complete, _ => unreachable!("invalid Once state"), }}''','PV_DIAG4.onceState',
 ['exclusive AtomicU32::get_mut loads caller-owned word','match 3 incomplete, 2 poisoned, 0 complete','other words retain invalid-state panic operation'],['all invalid-state panic/hook/abort effects stay P; source read representation V370'])
for n,v in [('INCOMPLETE','3'),('POISONED','2'),('COMPLETE','0')]:assert f'const {n}: Primitive = {v};' in (R/'std/src/sys/sync/once/futex.rs').read_text()
add('os_interrupted','std/src/sys/io/error/unix.rs','pub fn is_interrupted(', 'pub fn is_interrupted(errno: i32) -> bool { errno == libc::EINTR }','PV_DIAG4.osInterrupted', ['compare STORED raw i32 argument with Linux EINTR','return Bool; no errno TLS access'],['valid raw-code bit representation, libc constant selection, V370'])
# Complete destructor/decoder regions are retained. These have a remaining
# unsafe representation obligation, so are not represented as full restoration.
for name,path,marker,model in [
 ('repr_drop','std/src/io/error/repr_bitpacked.rs','impl Drop for Repr','PV_DIAG4.errorReprDrop'),
 ('repr_decode','std/src/io/error/repr_bitpacked.rs','unsafe fn decode_repr<','PV_DIAG4.errorTag / ValidErrorRepr'),
 ('repr_os_constructor','std/src/io/error/repr_bitpacked.rs','pub(super) fn new_os(','PV_DIAG4.osWord'),
 ('lazy_drop','std/src/sync/lazy_lock.rs','impl<T, F> Drop for LazyLock','PV_DIAG4.lazyDropWord')]:
 r=region(R/path,marker);b.append(dict(name=name,source=r,model=model,steps=['tag/state branch selection; custom or selected field full destructor retained; noncustom or poisoned branch has no owned field drop'],open_native_obligations=['validity/provenance/kind decoding and concrete field/Box/allocator operations outside the proved noncustom/poisoned branches; V370']))
# Linux libc constant is checked against the dependency source compiled in the deployed build.
lock=tomllib.loads((R/'Cargo.lock').read_text());package=next(p for p in lock['package'] if p['name']=='libc')
assert package['version']=='0.2.178'
libc=list(Path('/home/dombarker/.cargo/registry/src').glob('*/libc-0.2.178/src/unix/linux_like/linux/mod.rs'));assert len(libc)==1
p=libc[0];assert re.search(r'pub const EINTR:\s*c_int\s*=\s*4;',p.read_text())
archives=list(Path('/home/dombarker/.cargo/registry/cache').glob('*/libc-0.2.178.crate'));assert len(archives)==1
checksum=archives[0];assert sha(checksum)==package['checksum']
with tarfile.open(checksum) as archive: assert hashlib.sha256(archive.extractfile('libc-0.2.178/src/unix/linux_like/linux/mod.rs').read()).hexdigest()==sha(p)
constants=[dict(path=str(p),sha256=sha(p),constant='EINTR=4',stdlib_lock=str(R/'Cargo.lock'),stdlib_lock_sha256=sha(R/'Cargo.lock'),package=package,checksum_source=str(checksum),checksum_sha256=sha(checksum))]
# Complete active bodies: syscall and errno-location keep their own execution.
for name,path,marker,model in [
 ('fd_write','std/src/sys/fd/unix.rs','pub fn write(&self, buf: &[u8])','PV_DIAG4.rawFdWrite'),
 ('cvt','std/src/sys/pal/unix/mod.rs','pub fn cvt<T: IsMinusOne>','PV_DIAG4.rawCvt'),
 ('last_os_error','std/src/io/error.rs','pub fn last_os_error()','PV_DIAG4.lastOsError'),
 ('from_raw_os_error','std/src/io/error.rs','pub fn from_raw_os_error(','ValidErrorRepr.os / osWord'),
 ('errno','std/src/sys/io/error/unix.rs','pub fn errno()','PV_DIAG4.readErrno')]:
 r=region(R/path,marker);b.append(dict(name=name,source=r,model=model,
 steps=['source stores/argument evaluation and Result branch follow the model','syscall and errno_location remain full explicit operations','normal errno-location prefix is retained before the load and OS constructor','dropInterrupted uses proved OS-repr destructor, never formats or captures'],
 open_native_obligations=['native pointer/memory/ABI association, syscall/errno-location laws and joint external outcomes remain P; V370']))

exe=D/'native-controls'
out=dict(classification='own-1 statement-level source association; local emission laws only',bindings=b,libc_constant_authority=constants,generated_models={p.stem:sha(p) for p in (D/'sources').glob('PV_DIAG4_*.lean')},release_cfg_note='debug_assert in Repr::new_os/decode is inactive; invalid unsafe representation remains outside admitted memory domain',compiler_boundary='V370 / D381/D386 retained',native_validation='finite validation, std-only 1.94.1 optimized harness; no whole-run or singleton-domain claim',native_source_sha256=sha(D/'PV_DIAG4_NativeControls.rs'),native_binary_sha256=sha(exe),native_binary_bytes=exe.stat().st_size,rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-Vv'],text=True),profile=dict(opt_level=3,debug_assertions=False,overflow_checks=False,panic='unwind'),features='std-only harness: no application crate or dependency feature selection; deployed full application units inherited by hash',deployed_units_sha256=sha(D.parent/'codex-pv-diag-20261029/resolved-build-units.json'),deployed_binary='fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348',restored_endpoint_rows=[],whole_native_joint_law=False)
(D/'leaf-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print('bound',len(b),'source bodies; full honest native joint law remains open')
