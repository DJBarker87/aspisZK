"""Read-only own-1 source/dataflow association, not an execution or independence proof."""
from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag7-20261029')
P=D.parent/'codex-pv-diag3-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
b=json.loads((P/'binding.json').read_text()); rows=[]
for name,r in b['all_regions'].items():
 p=Path(r['path']);assert sha(p)==r['file_sha256'],name
 whole=p.read_text();text=r['text'];start=whole.find(text)
 assert start>=0 and whole.count(text)==1,name
 actual_start=whole[:start].count('\n')+1
 assert actual_start==r['line_start'],name
 rows.append(dict(name=name,path=str(p),file_sha256=sha(p),span=[actual_start,actual_start+len(text.splitlines())-1],historical_end_label=r['line_end'],body_sha256=hashlib.sha256(text.encode()).hexdigest()))
root=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
def region(path,start,end,checks):
 p=root/path;text=''.join(p.read_text().splitlines(keepends=True)[start-1:end]);last=-1
 for c in checks:
  i=text.find(c,last+1);assert i>=0,(path,c);last=i
 rows.append(dict(name=str(path),path=str(p),file_sha256=sha(p),span=[start,end],body=text,body_sha256=hashlib.sha256(text.encode()).hexdigest(),ordered_checks=checks))
region(Path('std/src/io/stdio.rs'),1155,1180,['fn print_to','if print_to_buffer_if_capture_used(args)','return;','global_s().write_fmt(args)','panic!("failed printing to {label}: {e}")','fn print_to_buffer_if_capture_used','OUTPUT_CAPTURE_USED','OUTPUT_CAPTURE.try_with','s.take().map','write_fmt(args)','s.set(Some(w))'])
p=D/'state_only_entropy.rs'
assert sha(p)=='4f6967771c5b7aaaebbd2967c6db1561e2d69de6c4c0f06f8d48a90f6d7ac2f7'
text=''.join(p.read_text().splitlines(keepends=True)[964:1018])
checks=['pub fn reserve_fallible','self.last_error = None','self.reservation_path(&mask_nonce)','options.write(true).create_new(true)','options.open(path)','AlreadyExists => return Ok(false)','Err(error) => return Err(error)','file.write_all(RESERVATION_MAGIC)?','file.write_all(&statement_digest)?','file.write_all(&mask_nonce)?','file.sync_all()?','sync_directory(&self.directory)?','Ok(true)','fn reserve(','self.reserve_fallible','Ok(reserved) => reserved','self.last_error = Some(error.kind())','false']
last=-1
for c in checks:
 i=text.find(c,last+1);assert i>=0,c;last=i
rows.append(dict(name='nonce_reserve_and_wrapper',path=str(p),file_sha256=sha(p),span=[965,1018],body=text,ordered_checks=checks,body_sha256=hashlib.sha256(text.encode()).hexdigest(),source_authority='diag-1 source-identity.json deployed feature body hash, same candidate bytes',remaining='reservation path derives from mask_nonce; written nonce/digest bytes are NOT public environment outcomes. V337/V338/V400 must bind their reached OS fault history; no nonce file is touched.'))
# The global state and call-site capture are deliberately NOT inferred public.
(D/'source-bindings.json').write_text(json.dumps(dict(evidence_class='own-1 environmental-input dataflow association; incomplete whole native binding',inherited_source=sha(P/'binding.json'),regions=rows,resolved_build_units=b['resolved_build_units'],deployed_rustc=b['deployed_rustc'],compiler_boundary='V370 / pending D381/D386',P_row='D215 / V400',mapping={
 'unix_fd_write':'signal.write fd cursor; supplied bytes, length and fd remain public-operand obligations; actual permitted return range retained',
 'write_all':'PV_DIAG7.writeOps / existing writeAllStep and writePrefix; partial writes, zero, Interrupted guard/drop and actual supplied suffix retained',
 'print_to':'public capture configuration then global write_fmt; failure guard from OS reply; label and OS error text public when operands are public; full panic hook/payload/frames NOT covered',
 'nonce_file':'signal.file op cursor models status only; public path/operation/history required; successful reads/secret contents excluded; nonce lifecycle E2 V337/V338 retained',
 'last_error':'signal.errno cursor and explicit State.lastError slot; shared-history/OS representation association retained',
 'logger':'signal.environment/loggerEnabled/loggerRoute only; mutable logger/TLS/locks and arbitrary logger body excluded',
 'backtrace':'configuration selection only; no signal field contains captured PCs or witness control paths',
 'strerror_lossy':'signal.strerror code then public pure lossy renderer; selected code and invocation must be public; native encoding association retained'
},removed_native_hypotheses=0,new_trust_items=0),indent=2)+'\n')
print('source regions rechecked',len(rows),'V400 retained; full binding false')
