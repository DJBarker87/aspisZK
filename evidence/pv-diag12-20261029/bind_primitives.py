from pathlib import Path
import json,hashlib,re,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-diag12-20261029')
S=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=['std/src/sync/reentrant_lock.rs','std/src/sys/sync/mutex/futex.rs','std/src/sys/sync/futex/linux.rs','std/src/io/mod.rs','std/src/io/error.rs','std/src/io/error/repr_bitpacked.rs','core/src/ub_checks.rs','core/src/fmt/mod.rs','std/src/sys/pal/common/small_c_string.rs']
rows=json.loads((D/'rust-src-pins.json').read_text())
for f in paths:
 p=S/f
 if not p.exists():continue
 dst=D/('source-'+f.replace('/','_')+'.txt');dst.write_bytes(p.read_bytes());rows.append(dict(path=str(p),snapshot=dst.name,sha256=sha(p)))
for r in rows:assert sha(Path(r['path']))==r['sha256'] and sha(D/r['snapshot'])==r['sha256']
(D/'rust-src-pins.json').write_text(json.dumps(rows,indent=2)+'\n')
F=D.parent/'codex-pv-fscan-20261028/src';lock=F/'tools/r1-cost-probe/Cargo.lock'
version=re.search(r'name = "serde_json"\nversion = "([^\"]+)"',lock.read_text())[1]
reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
js=[]
for f in ['src/value/mod.rs','src/value/ser.rs','src/ser.rs']:
 p=reg/('serde_json-'+version)/f;dst=D/('source-serde_json-'+f.replace('/','_')+'.txt');dst.write_bytes(p.read_bytes());js.append(dict(path=str(p),snapshot=dst.name,sha256=sha(p)))
(D/'serde-json-pins.json').write_text(json.dumps(dict(version=version,lock_sha256=sha(lock),sources=js),indent=2)+'\n')
# Recheck the frozen client identity chain; no edit or native client execution.
pins=json.loads((D.parent/'codex-pv-diag-20261029/source-identity.json').read_text())['checks']
for r in pins:assert sha(F/r['path'])==r['sha256']
# Record source spans and corresponding model equations; this is independently
# inspectable structural evidence, not an automated proof of the residual calls.
bindings=[]
def row(name,file,start,end,steps,residual):
 p=D/file;s=p.read_text();a=s.index(start);b=s.index(end,a)+len(end);body=s[a:b]
 for token,model in steps:assert token in body,(name,token)
 bindings.append(dict(name=name,snapshot=file,sha256=sha(p),body_sha256=hashlib.sha256(body.encode()).hexdigest(),start_line=s[:a].count('\n')+1,end_line=s[:b].count('\n')+1,steps=[dict(rust=t,lean=m) for t,m in steps],residual=residual,complete_syscall_binding=False))
row('FileDesc::write','source-sys_fd_unix.rs.txt','    pub fn write(&self, buf:', '\n    }',[
 ('libc::write(','fdWrite / one write ABI request'),('self.as_raw_fd()','Request.write fd'),('buf.as_ptr()','Span.base / offset'),('cmp::min(buf.len(), READ_LIMIT)','min len linuxReadLimit'),('cvt(unsafe','Reply returned/error and errno conversion'),('Ok(ret as usize)','Result.ok n')],['libc write and errno TLS to exact kernel requests/results','valid pointer/range representation and foreign-contract returned count','READ_LIMIT Linux x86_64 cfg selection; machine code V370 / D381 / D386'])
row('sys::File::flush','source-sys_fs_unix.rs.txt','    pub fn flush(&self)', '\n    }', [('Ok(())','fdFlush, no fsync')],['fd/state source association; V370'])
row('sys::File::open_c','source-sys_fs_unix.rs.txt','    pub fn open_c(', '\n    }', [('libc::O_CLOEXEC','openFlags 524288'),('opts.get_access_mode()?','access options'),('opts.get_creation_mode()?','creation options'),('opts.custom_flags as c_int & !libc::O_ACCMODE','custom u32 mask 4294967292'),('cvt_r(|| unsafe { open64','openRetry preserving EINTR request/result records'),('opts.mode as c_int','Request.open64 mode'),('FileDesc::from_raw_fd(fd)','valid fd constructor')],['path/CStr conversion allocation and invalid NUL handling','io::Error::new validation allocation/drop/abort','libc open64 cancellation/TLS and actual openat requests','native constructor/frame association and V370'])
row('OwnedFd::drop','source-os_fd_owned.rs.txt','    fn drop(&mut self)', '\n    }', [('debug_assert_fd_is_open','explicit precondition: UB checker disabled for fdDrop model'),('let _ = libc::close','fdDrop ignored response and no retry')],['core::intrinsics::ub_checks specialization; if enabled fcntl + abort path','libc close cancellation/TLS / syscall expansion','native drop glue and unwind prefixes; V370'])
row('StdoutRaw::write/all','source-io_stdio.rs.txt','impl Write for StdoutRaw','\nimpl Write for StderrRaw', [('handle_ebadf(self.0.write(buf), || Ok(buf.len()))','stdWrite / success does not imply delivery'),('handle_ebadf(self.0.write_all(buf), || Ok(()))','stdWriteAll masks around full inner loop, once'),('handle_ebadf(self.0.flush(), || Ok(()))','fdFlush')],['std/sys forwarding and raw error representation/drop; allocation for non-raw errors','all ABI-to-kernel residuals inherited'])
row('BufWriter::flush_buf','source-io_buffered_bufwriter.rs.txt','    pub(in crate::io) fn flush_buf(', '\n    /// Buffer some data', [('struct BufGuard','flushLoop remaining view; flushBuf normal rebase'),('self.buffer.drain(..self.written)','rebaseBuffer + remaining content, physical memory still open'),('self.panicked = true','in-flight flag'),('self.inner.write(guard.remaining())','stdWrite fd of remaining view'),('self.panicked = false','ordinary reply restores flag'),('Ok(0)','model WriteZero -1'),('Ok(n) => guard.consume(n)','advance symbolic span'),('Err(ref e) if e.is_interrupted()','same view/new signal cursor'),('Err(e) => return Err(e)','error + written prefix retained')],['actual Vec drain/copy addresses and memory state, live BufGuard, unwinding and native abort','model -2 denotes violated Write contract, not native panic/hook','fuel cut is not native divergence; emitted prefix association open'])
row('BufWriter::drop','source-io_buffered_bufwriter.rs.txt','impl<W: ?Sized + Write> Drop for BufWriter<W>', '\n}', [('if !self.panicked','bufferDrop guard'),('let _r = self.flush_buf()','ignore returned error, preserve requests/results and cut')],['inner/Vec destruction after body, native panic/OOM/unwind/drop glue'])
row('LineWriterShim::write_all','source-io_buffered_linewritershim.rs.txt','    fn write_all(', '\n    }', [('memchr::memrchr','lastNewline'),('self.flush_if_completed_line()?','flushCompleted'),('self.buffer.write_all(buf)','bufferedAll no-newline'),('buf.split_at(newline_idx + 1)','lineSpan and advance'),('self.buffered().is_empty()','empty/nonempty buffer case'),('self.inner_mut().write_all(lines)?','directAll'),('self.buffer.write_all(lines)?','bufferedAll'),('self.buffer.flush_buf()?','flushBuf'),('self.buffer.write_all(tail)','bufferedAll tail')],['native scan/slice/store/borrow and allocation/midcall state association','capacity/pointer/drain association and inherited syscall residuals'])
row('stdout lock/write_fmt','source-io_stdio.rs.txt','impl Write for &Stdout','\nimpl Write for StdoutLock', [('self.lock().write_fmt(args)','whole fmt under one lock')],['OnceLock and allocation, ReentrantLock owner/TLS/thread_id/futex contention/overflow','RefCell borrow and guard drop, native callbacks/reentrancy, capture','fmt specialization and JSON Value Display streaming'])
(D/'primitive-bindings.json').write_text(json.dumps(dict(rows=bindings,source_inputs_checked=len(pins),toolchain='1.94.1',target='x86_64-unknown-linux-gnu',profile='release',features=['r1p-check','aspis-r1-cost-probe/ct-host-prover'],compiler_boundary='V370 / D381 / D386 retained',evidence_class='own-1 source-body associations for listed control; explicitly incomplete transitive syscall binding',endpoint_premises_removed=0),indent=2)+'\n')
# Supporting ABI/runtime identity only: no claim disassembly is a source proof.
libc=Path('/lib/x86_64-linux-gnu/libc.so.6')
cmd=['objdump','-d','--disassemble=__write',str(libc)]
r=subprocess.run(cmd,text=True,capture_output=True)
(D/'libc-write-disassembly.txt').write_text(r.stdout+r.stderr)
(D/'libc-identity.json').write_text(json.dumps(dict(path=str(libc),sha256=sha(libc),command=cmd,exit=r.returncode,status='supporting evidence; exact libc syscall expansion unproved'),indent=2)+'\n')
print('bound source associations',len(bindings),'std snapshots',len(rows),'serde_json',version,'frozen inputs',len(pins))
