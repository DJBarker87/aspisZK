"""Pin deployed class-B bodies and bind every outer control step to an
explicit model step/complete leaf. Open leaf/drop/foreign laws stay P.
"""
from pathlib import Path
import json,hashlib,sys,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library');A=next(Path('/home/dombarker/.cargo/registry/src').glob('index.crates.io-1949*/anyhow-1.0.104/src'));L=next(Path('/home/dombarker/.cargo/registry/src').glob('index.crates.io-1949*/log-0.4.34/src'))
family=sys.argv[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def body(p,needle):
 text=p.read_text();m=re.search(r'(?m)^[ \t]*'+re.escape(needle),text);assert m,(p,needle);a=m.start();j=text.index('{',a);k=j+1;depth=1
 while depth:depth+=(text[k]=='{')-(text[k]=='}');k+=1
 return dict(path=str(p),file_sha256=sha(p),line=text[:a].count('\n')+1,body=text[a:k])
if family=='capture':
 rows=[body(R/'std/src/backtrace.rs',s) for s in ['fn enabled() -> bool','pub fn capture() -> Backtrace','pub fn force_capture() -> Backtrace','pub const fn disabled() -> Backtrace']]
 text=rows[0]['body'];assert 'ENABLED.load(Relaxed)' in text and 'ENABLED.store(enabled as u8 + 1, Relaxed)' in text
 assert text.index('RUST_LIB_BACKTRACE')<text.index('RUST_BACKTRACE')
 models=['PV_DIAG2_BacktraceFlags','PV_DIAG2_CaptureControl'];steps=[
 ['atomic cache load and cached1/_ returns','enableStep / enabledExecution.load','cache input is the actual observed load, not invented final concurrent memory'],
 ['cache0 library env read; Ok(s) s!="0"; Err(_) fallback read','chooseEnv / readBacktraceEnv.library/fallback','library and fallback executions retain their own allocation/OS/panic effects'],
 ['owned String/VarError comparison and drops','closeLibrary / closeFallback','native lexical scopes and unwind/failure cleanup remain explicit supplied continuations; not identity'],
 ['atomic store bool-as-u8+1 and return','cacheCode / enabledExecution.store','requested code proved1or2; relaxed concurrency law remains open'],
 ['capture enabled false => Inner::Disabled','captureExecution false','no Backtrace::create call after normally completed false flag; earlier env effects remain'],
 ['capture enabled true => create(ip)','captureExecution create','create includes lock, allocations, unwinder, image-base, frames, actual_start, cleanup and runtime outcomes'],
 ['force_capture bypasses enabled; disabled const returns Disabled','forceCaptureExecution / BacktraceValue.disabled','neither proves global absence of other callers or native frames publicness']]
 open_leaves=['native env/comparison/drop-scope executions','Backtrace::create and allocator/unwinder/image/module closure','actual PC lists and concurrent environment/cache-history law']
elif family=='print':
 rows=[body(R/'std/src/io/stdio.rs',s) for s in ['fn print_to<T>','fn print_to_buffer_if_capture_used','pub(crate) fn attempt_print_to_stderr']]
 assert 'panic!("failed printing to {label}: {e}")' in rows[0]['body'];assert 'let _ = stderr().write_fmt(args)' in rows[2]['body']
 models=['PV_DIAG2_PrintControl','PV_DIAG2_Termination'];steps=[
 ['print_to buffer capture check and early return','printTo.capture true','whole capture helper effects retained; argument evaluation before this helper remains earlier prefix'],
 ['global_s getter, write_fmt and temporary handle scope','printTo.write','full getter/write/partial-delivery/temporary-drop/native-unwind execution supplied'],
 ['Err(e) panic formatting/hook and Err lifetime','printTo.panic e','includes the error Display operand, actual frames and Err drop/unwind; not a normal error report'],
 ['normal Ok returned write result','print_write_ok','capture and write prefixes retained'],
 ['attempt_print_to_stderr capture then ignored write Result','attemptPrint / ignoreWriteResult / terminateOwned','Result and handle drops are native leaf executions; no panic invented on returned I/O error']]
 open_leaves=['capture helper atomic/TLS/mutex/poison/write/restore/drop execution','global getter and delivered-byte/partial-I/O law','I/O error Display, panic/OOM/unwind/drop/native failure independence']
elif family=='anyhow':
 rows=[body(A/'fmt.rs','pub(crate) unsafe fn debug'),body(A/'error.rs','impl Debug for Error'),body(A/'error.rs','pub(crate) fn construct_from_adhoc'),body(A/'error.rs','impl Drop for Error'),body(A/'wrapper.rs','impl<M> Debug for MessageError'),body(A/'wrapper.rs','impl<M> Display for MessageError')]
 wrapper=(A/'wrapper.rs').read_text();assert "impl<M> StdError for MessageError<M> where M: Display + Debug + 'static {}" in wrapper
 default_source=body(R/'core/src/error.rs',"fn source(&self)")
 assert 'None' in default_source['body'];rows.append(default_source)
 fmt=rows[0]['body'];assert fmt.index('if f.alternate()')<fmt.index('write!(f, "{}", error)?')<fmt.index('if let Some(cause)')<fmt.index('backtrace.status()')
 models=['PV_DIAG2_AnyhowDebugControl','PV_DIAG2_ErrorText','PV_DIAG2_Termination'];steps=[
 ['Error Debug forwards to ErrorImpl::debug','messageDebug','anyhow pointer/formatter state supplied by S; compiler and memory/source association remain named'],
 ['alternate => Debug::fmt(error)','MessageDebugOps.alternate','underlying quoted String or str Debug execution; never conflated with ordinary Debug'],
 ['ordinary write Display(error)?','MessageDebugOps.display / writerBind','mutable formatter state retained even on returned fmt::Error; partial effects kept'],
 ['MessageError<String/str> source() is default None','specialized no-cause control','literal format_err Error::msg constructs MessageError, not a contextual cause chain; other anyhow constructors not covered'],
 ['read backtrace/status','MessageDebugOps.getBacktrace','includes missing-backtrace expect panic if reached; no assumed successful getter'],
 ['Captured branch to_string/newlines/starts_with/replace_range/trim/truncate/write/drop','MessageDebugOps.captured','whole branch explicitly supplied with mutated state, errors, OOM, panic, actual PCs/symbolization and string drops'],
 ['noncaptured return Ok(())','debug_not_captured','message Display leaf is still needed for actual delivered bytes'],
 ['object Drop via vtable','terminateOwned.dropError/unwindError','owned message/backtrace frees and panic cleanup are not declared silent']]
 open_leaves=['String formatter/allocator/partial writes and state refinement','captured branch symbolization/cache/unwinder/cleanup effects','construct_from_adhoc allocation/vtable/memory source law and error Drop','normal fixed requested text is not a full stderr failure/frame law']
elif family=='log':
 rows=[body(L/'macros.rs','macro_rules! __log'),body(L/'lib.rs','pub fn max_level()')]
 text=rows[0]['body'];assert text.count('if lvl <= $crate::STATIC_MAX_LEVEL && lvl <= $crate::max_level()')==2
 lib=(L/'lib.rs').read_text();assert 'static MAX_LOG_LEVEL_FILTER: AtomicUsize = AtomicUsize::new(0);' in lib
 units=json.loads((D.parent/'codex-pv-diag-20261029/resolved-build-units.json').read_text());unit=next(r for r in units['units'] if '/log-' in r['path']);assert unit['record']['features']=='[]'
 models=['PV_DIAG2_LogControl'];steps=[
 ['let lvl=$lvl','logMacro.level','level-expression effects retained; a disabled macro does not erase its earlier effects'],
 ['static max comparison, short circuit','logMacro staticMax=5','features[] + release => STATIC_MAX_LEVEL Trace'],
 ['max_level AtomicUsize relaxed load','logMacro.loadMax','source initial0 Off; no global proof that dependencies never call set_max_level'],
 ['runtime max comparison, short circuit','log_runtime_off_skips_arguments','Level Error..Trace are1..5; max0 suppresses subsequent argument construction/dispatch'],
 ['logger/format_args/target/location/kv values and private log call','logMacro.dispatch','all native argument evaluation, Record builder state, logger calls/output and temporary cleanup retained; kv feature disabled']]
 open_leaves=['global filter/logger configuration stability and complete caller closure','actual level expression provenance','enabled dispatch argument/content/output and foreign logger effects'];rows.append(dict(path=unit['path'],fingerprint=unit))
elif family=='panic-oom':
 rows=[body(R/'std/src/alloc.rs','fn default_alloc_error_hook'),body(R/'std/src/alloc.rs','pub fn rust_oom'),body(R/'std/src/panicking.rs','fn default_hook'),body(R/'std/src/panic.rs','pub fn get_backtrace_style')]
 assert 'crate::process::abort()' in rows[1]['body'];assert 'layout.size()' in rows[0]['body']
 models=['PV_DIAG2_Effects','PV_DIAG2_Process','PV_DIAG2_Termination'];steps=[
 ['OOM previous-allocation-failure atomic swap and recursion message','runtime OOM leaf remains open','size field retained; no constant/public-size theorem'],
 ['panic_output, backtrace lock and Short/Full/Off/None style branches','runtime hook leaf remains open','actual writes, style/environment/cache, mutex drop and frame lists not erased'],
 ['rust_oom hook selection, invoke hook, process::abort','runtime OOM/foreign closure remains open','original Terminal lacks distinct abort/crash-memory carrier; no complete native fatal-refinement claim'],
 ['default panic hook thread/location/payload/output/style/frames','runtime panic leaf remains open','panic frame source differs from post-return plan::err capture; honest guard not excluded']]
 open_leaves=['complete native panic/OOM/hook/double-panic/abort representation and source association','failure occurrence and allocation sizes/frames provenance','raw bytes, foreign writes, delivered stderr and configured crash-memory/register reports']
else:raise ValueError(family)
for module in models:assert (D/'sources'/(module+'.lean')).is_file()
result=dict(family=family,classification='deployed-source outer-frame structural binding under own-1; open native leaf and ownership laws are not restored rows',sources=rows,models={m:sha(D/'sources'/(m+'.lean')) for m in models},steps=steps,open_native_obligations=open_leaves,toolchain='rustc 1.94.1 sources; no extractor/toolchain substitution',profile='deployed release opt3 overflow/debug assertions off panic unwind',compiler_boundary='V370 at owner pending D381/D386; no LLVM or machine equality silently assumed',new_trust_fields=0)
(D/(family+'-body-binding.json')).write_text(json.dumps(result,indent=2)+'\n');print('pinned',family,'complete bodies',len(rows),'outer steps',len(steps),'open leaf families',len(open_leaves))
