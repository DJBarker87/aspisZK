from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag5-20261029');R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
token=re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\{|\}|[^{}"/]+|.',re.S)
def region(path,marker):
 text=path.read_text();at=text.index(marker);body=text.index('{',at);depth=0
 for m in token.finditer(text,body):
  if m.group()=='{':depth+=1
  elif m.group()=='}':
   depth-=1
   if not depth:return dict(path=str(path),file_sha256=sha(path),line=text[:at].count('\n')+1,text=text[at:m.end()])
 raise AssertionError(marker)
p=R/'std/src/backtrace.rs';assert sha(p)=='b1d5bdb5db8b622ab022ac0d6d29b6022b5b4a1001e6c5d28c66ca81d9ae262a'
rows=[]
def add(name,marker,model,steps,remaining):
 rows.append(dict(name=name,source=region(p,marker),model=model,statement_mapping=steps,retained_P=remaining))
add('disabled','pub const fn disabled()', 'PV_DIAG5.disabledTrace', ['return Inner::Disabled; no frame ownership, allocation, callee, drop or external reads'],['V370'])
add('capture','pub fn capture()', 'PV_DIAG5.captureTrace', ['call Backtrace::enabled complete native operation','normal false: construct disabled; no create','normal true: call create with capture function address','all abnormal prefixes retained'],['enablement cache/env/TLS and complete create association; V370'])
add('force_capture','pub fn force_capture()', 'PV_DIAG5.forceTrace', ['call create with force_capture function address, unconditionally','function address is not an arbitrary common constant'],['complete create association and address identity; V370'])
add('create','fn create(ip: usize)', 'PV_DIAG5.callback / capturedFrames / actual_display_slice_valid', [
 'lock guard acquired before frame vector; Vec::new and None initialize state',
 'set_image_base retains complete effects; foreign trace driver selects raw frame sequence',
 'each callback: clone original raw frame; build RawFrame::Actual and zero-capacity symbols Vec; push with allocation/drop/error effects',
 'query symbol_address on ORIGINAL borrowed frame after push, then compare addr with ip',
 'only when equal AND actual_start None: assign Some(POST-PUSH length); return true normally',
 'finite normally completed callbacks give frame order and start bound by proved list induction',
 'empty frames => unsupported; nonempty moves capture into lazy_resolve then LazyLock',
 'actual lock/frame/closure drops and failed move ownership retained in explicit native state; these are not proved silent'
 ],['lock,image base,unwinder,clone/push/address/package/drop/unwind native operation laws; raw-frame joint distribution; V370'])
add('display','impl fmt::Display for Backtrace', 'PV_DIAG5.emitFrame / displayTrace', [
 'borrow unsupported/disabled => write corresponding literal and RETURN its full formatter Result',
 'captured => force LazyLock; read alternate; full uses all frames and Full style; short uses actual_start suffix and Short style',
 'actual_display_slice_valid discharges short slice panic for states made by finite normally completed create callbacks',
 'current_dir executed even for full; move cwd Result into closure; failed cwd is not propagated as formatting failure',
 'BacktraceFmt new; add_context ?; iterate selected borrowed frames in order',
 'empty symbols => print_raw(ip,None,None,None) ?; else each symbol print_raw_with_column(ip,name,filename,line,column) ?',
 'finish ?; return Ok; guard/formatter/cwd cleanup on normal and unwind, abort does not unwind'
 ],['lazy resolve/current_dir/formatter/write/drop full operation laws and joint native occurrence/content; V370'])
add('lazy_resolve','pub(super) fn lazy_resolve(mut capture: Capture)', 'retained native obligation', [
 'closure owns capture; acquire global backtrace lock when FORCED, not when constructed',
 'mutable iteration resolves each frame and PUSHES every symbol including copied name,filename,line,column',
 'all writes through mutable borrowed frame/symbol vector must be retained; no Aeneas iterator-restoration credit claimed',
 'normal return MOVES capture; drop guard unlocks; panic has actual closure/frame/vector/lock cleanup'
 ],['complete resolver foreign/cache/image/debug-file and allocation/writeback law; V370'])
(D/'source-bindings.json').write_text(json.dumps(dict(classification='own-1 statement-level structural association; callee obligations explicitly retained',bindings=rows,source_to_machine='V370 / pending D381/D386',whole_native_joint_law=False),indent=2)+'\n')
print('checked',len(rows),'complete deployed source regions; V370 retained')
