"""Read-only deployed-source inventory and statement-level ownership binding.
This deliberately does not certify opaque callees or claim full-cone silence.
"""
from pathlib import Path
import hashlib,json,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag3-20261029')
R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
A=next(Path('/home/dombarker/.cargo/registry/src').glob('index.crates.io-*/anyhow-1.0.104/src'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Delimit complete source regions by two unique anchors. Keeping exact text
# allows review of statements, macros, scopes, stores and implicit cleanup.
specs=[
('write_all',R/'std/src/io/mod.rs','    fn write_all(&mut self, mut buf: &[u8])','    /// Attempts to write multiple buffers'),
('default_write_fmt',R/'std/src/io/mod.rs','pub(crate) fn default_write_fmt','/// The `Read` trait'),
('write_fmt',R/'std/src/io/mod.rs','    fn write_fmt(&mut self, args: fmt::Arguments','    /// Creates a "by reference"'),
('unix_stdio',R/'std/src/sys/stdio/unix.rs','impl Stderr {','pub fn is_ebadf'),
('unix_fd_write',R/'std/src/sys/fd/unix.rs','    pub fn write(&self, buf: &[u8])','    #[cfg(not(any('),
('backtrace_create_status',R/'std/src/backtrace.rs','    fn create(ip: usize)','impl<\'a> Backtrace'),
('backtrace_display',R/'std/src/backtrace.rs','impl fmt::Display for Backtrace','mod helper {'),
('backtrace_resolve',R/'std/src/backtrace.rs','mod helper {','use helper::*;'),
('anyhow_drop',A/'error.rs','impl Drop for Error {','// Safety: requires layout of *e to match ErrorImpl<E>.\nunsafe fn object_drop_front'),
('anyhow_layout',A/'error.rs','pub(crate) struct ErrorImpl<E = ()>','impl<E> ErrorImpl<E>'),
('anyhow_ptr',A/'ptr.rs','impl<T> Own<T>',"impl<'a, T> Copy for Ref"),
]
rows=[]
for name,p,start,end in specs:
 t=p.read_text();a=t.index(start);b=t.index(end,a+len(start));body=t[a:b]
 rows.append(dict(name=name,path=str(p),file_sha256=sha(p),line_start=t[:a].count('\n')+1,line_end=t[:b].count('\n')+1,text=body,text_sha256=hashlib.sha256(body.encode()).hexdigest()))
(D/'source-regions.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Pinned',len(rows),'deployed source regions; includes whole body and cleanup-bearing lexical scope')
