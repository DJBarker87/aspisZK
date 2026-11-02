from pathlib import Path
import json,re,hashlib,subprocess
D=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def body(s,anchor):
 a=s.index('{',s.index(anchor));depth=0
 for i in range(a,len(s)):
  depth+=(s[i]=='{')-(s[i]=='}')
  if depth==0:return s[a:i+1]
 raise ValueError(anchor)
def tok(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S))
fs=(D/'inputs/io/fs.rs').read_text();fd=(D/'inputs/io/fd-unix.rs').read_text();sysfs=(D/'inputs/io/fs-unix.rs').read_text();io=(D/'inputs/io/mod.rs').read_text();error=(D/'inputs/std-error.rs').read_text()
loop=body(io,'fn write_all(&mut self, mut buf:')
want='''{ while !buf.is_empty() { match self.write(buf) {
 Ok(0) => { return Err(Error::WRITE_ALL_EOF); }
 Ok(n) => buf = &buf[n..], Err(ref e) if e.is_interrupted() => {}
 Err(e) => return Err(e), } } Ok(()) }'''
checks={
 'complete_default_loop':tok(loop)==tok(want),
 'owned_file_uses_default_write_all':'fn write_all(' not in body(fs,'impl Write for File {'),
 'borrowed_file_uses_default_write_all':'fn write_all(' not in body(fs,'impl Write for &File {'),
 'owned_write_delegates':tok(body(body(fs,'impl Write for File {'),'fn write('))==tok('{ (&*self).write(buf) }'),
 'borrowed_write_delegates':tok(body(body(fs,'impl Write for &File {'),'fn write('))==tok('{ self.inner.write(buf) }'),
 'sys_file_write_delegates':tok(body(sysfs,'pub fn write(&self, buf:'))==tok('{ self.0.write(buf) }'),
 'fd_write_complete':tok(body(fd,'pub fn write(&self, buf:'))==tok('''{ let ret = cvt(unsafe { libc::write(self.as_raw_fd(),buf.as_ptr() as *const libc::c_void,cmp::min(buf.len(), READ_LIMIT),) })?; Ok(ret as usize) }'''),
 'writezero_static_message':'const WRITE_ALL_EOF: Self =\n        const_error!(ErrorKind::WriteZero, "failed to write whole buffer");' in error,
 'interrupted_uses_packed_data':tok(body(error,'pub(crate) fn is_interrupted('))==tok('''{ match self.repr.data() { ErrorData::Os(code) => sys::io::is_interrupted(code), ErrorData::Custom(c) => c.kind == ErrorKind::Interrupted, ErrorData::Simple(kind) => kind == ErrorKind::Interrupted, ErrorData::SimpleMessage(m) => m.kind == ErrorKind::Interrupted, } }'''),
 'os_interrupted_is_errno_only':tok(body((D/'inputs/std-unix-error.rs').read_text(),'pub fn is_interrupted('))==tok('{ errno == libc::EINTR }'),
 'negative_bounded_retry_rejected':'fuel' not in loop and 'retry_limit' not in loop,
}
model_path='evidence/pv-diag12-20261029/PV_DIAG12_WriteAll.lean'
b=subprocess.check_output(['git','show','HEAD:'+model_path]);(D/'inputs/io/PV_DIAG12_WriteAll.lean.txt').write_bytes(b)
checks['existing_model_has_explicit_prefix_cut']='| 0,_,c => ⟨⟨[],.cut⟩,c⟩' in b.decode()
p='docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean'
b2=subprocess.check_output(['git','show','HEAD:'+p]);(D/'inputs/io/ProverRwFullExternalFuns.lean.txt').write_bytes(b2)
report={'row':'V267','status':'OPEN','classification':'script-checked complete source dispatch census only, not an installed native op261 or a whole source/world proof','checks':checks,'ok':all(checks.values()),'source_chain':['default std::io::Write::write_all on owned File','File::write -> (&*self).write','&File::write -> self.inner.write','sys::fs::File::write -> FileDesc::write','FileDesc::write -> libc::write(fd,ptr,min(len,READ_LIMIT)); cvt -> errno/Error association'],'existing_consumer_signature':next(line for line in b2.decode().splitlines() if 'op261 :' in line),'exact_remaining_premise':'Instantiate that same op261 with complete Result/error/divergence and the returned File token in the same native post-world. Bind fd provenance/ownership, every libc write outcome and partial offset update, errno capture/cvt, OS Interrupted predicate, static WriteZero error, and all success/error/failure prefixes. Prove native count bounds (or retain the actual slice panic if not) rather than mapping contract violation to a new model error. Unbounded Interrupted traces need a completion/divergence relation; no finite fuel bound follows from the three public input lengths. Existing fuelled DIAG12 writeAll is a prefix model, not an exact native operation. V271, V370 and actual observer/world adequacy remain, without a new T field.','caller':'reserve_fallible writes RESERVATION_MAGIC, statement_digest, mask_nonce in that order, branches on each full Result, and syncs only after all writes succeed. Retain the existing Error/Drop/caller frame.','native_tools':'Direct extraction of the reached Error representation is already rejected by pinned ae1 (N90502). No unchanged translator failure was rerun. No bounded prefix is installed as the total op.','pins':{str(f.relative_to(D)):sha(f.read_bytes()) for f in (D/'inputs/io').glob('*') if f.is_file()},'premises_removed':0,'premises_added':0,'premises_weakened':0}
(D/'PV_O11_write-all.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'ok':report['ok'],'checks':len(checks),'failed':[k for k,v in checks.items() if not v]}));assert report['ok']
