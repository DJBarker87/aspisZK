"""own-1: exact deployed source control frames and explicit open leaf calls.
This certificate does not turn supplied leaf executions into native proofs.
"""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029')
R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
sha=lambda b:hashlib.sha256(b).hexdigest()
def body(text,begin):
 i=text.index(begin);j=text.index('{',i);depth=1;k=j+1
 while depth:
  depth+=(text[k]=='{')-(text[k]=='}');k+=1
 return text[i:k]
process=(R/'std/src/process.rs').read_text();stdio=(R/'std/src/io/stdio.rs').read_text()
expected='''impl<T: Termination, E: fmt::Debug> Termination for Result<T, E> {
    fn report(self) -> ExitCode {
        match self {
            Ok(val) => val.report(),
            Err(err) => {
                io::attempt_print_to_stderr(format_args_nl!("Error: {err:?}"));
                ExitCode::FAILURE
            }
        }
    }
}'''
actual=body(process,'impl<T: Termination, E: fmt::Debug> Termination for Result<T, E>')
assert actual==expected
attempt='''pub(crate) fn attempt_print_to_stderr(args: fmt::Arguments<'_>) {
    if print_to_buffer_if_capture_used(args) {
        return;
    }

    // Ignore error if the write fails, for example because stderr is already
    // closed. There is not much point panicking at this point.
    let _ = stderr().write_fmt(args);
}'''
assert body(stdio,'pub(crate) fn attempt_print_to_stderr(')==attempt
unit=body(process,'impl Termination for ()');assert 'ExitCode::SUCCESS' in unit
steps=[
 dict(source='match self, Ok(val)',model='terminateOwned .ok ()',law='termination_success',leaf='Unit::report = ExitCode::SUCCESS; Unit drop has no glue'),
 dict(source='Err(err), format_args_nl!("Error: {err:?}")',model='report e',leaf='Borrowed arguments/normal anyhow Debug formatting are supplied by report; no formatting is performed eagerly by format_args_nl'),
 dict(source='print_to_buffer_if_capture_used(args)',model='attemptPrint capture globalWrite',law='captured_no_global / uncaptured_global / capture_panic / capture_oom',leaf='Whole atomic/thread-local/capture/lock/poison/write/restoration/drop/unwind execution remains capture'),
 dict(source='true => return',model='pureExecution () after retained capture effects',law='captured_no_global'),
 dict(source='false => stderr().write_fmt(args)',model='globalWrite',leaf='stderr getter, Write::write_fmt, formatting, partial delivery and temporary handle cleanup are supplied, not empty'),
 dict(source='let _ = <write Result>',model='ignoreWriteResult write dropResult inside globalWrite',law='ignored_io_error',leaf='Result/io::Error drop, handle drop and all abnormal cleanup retained'),
 dict(source='ExitCode::FAILURE; end Err arm scope',model='dropError then pureExecution 1',law='report_then_drop / normal_error_exit',leaf='Anyhow err object Drop (vtable object_drop, owned message/backtrace frees) remains dropError'),
 dict(source='reporter unwinds/panics/OOM/diverges',model='prepend body.effects (unwindError e abnormal)',law='report_panics_unwind',leaf='Complete cleanup/hook/abort reporting supplied by unwindError; no ordinary success inferred'),
]
result=dict(classification='structural class-B outer control binding under own-1; open native leaf executions remain P',toolchain='rustc 1.94.1',profile='release; overflow/debug assertions off; panic unwind',features='std; caller devnet_spend r1p-check,aspis-r1-cost-probe/ct-host-prover; dependency features in inherited resolved-build-units.json',source_files={str(R/'std/src/process.rs'):sha(process.encode()),str(R/'std/src/io/stdio.rs'):sha(stdio.encode())},complete_bodies=dict(result_termination=actual,unit_termination=unit,attempt_print_to_stderr=attempt),steps=steps,model_sha256=sha((D/'sources/PV_DIAG2_Termination.lean').read_bytes()),retained_boundaries=['V370 compiler preservation at owner pending D381/D386 compiler-cohort boundary','native executions of all listed leaf/drop/unwind interfaces','raw-byte/abort/crash-memory coverage not established by the original string carrier'],new_trust_fields=0)
(D/'termination-structural-binding.json').write_text(json.dumps(result,indent=2)+'\n');print('bound complete Result/Unit Termination and attempt_print outer bodies; all leaf/drop/unwind obligations explicit')
