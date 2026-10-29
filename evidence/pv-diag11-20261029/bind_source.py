from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag11-20261029');P=D.parent/'codex-pv-diag10-20261029';S=D.parent/'codex-pv-fscan-20261028/src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ext=json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())
for r in ext:assert sha(Path(r['path']))==r['object_sha256'],r['path']
(D/'external-preflight.json').write_text(json.dumps(dict(checked=len(ext),mismatches=[],authority=str(D.parent/'codex-pv-diag5-20261029/external-authority.json'),timing='independent live check before 67079 and final source extensions; initial compiles relied on inherited authority without independent live external check'),indent=2)+'\n')
for r in json.loads((D/'reuse.json').read_text())['rows']:
 assert sha(Path(r['path']))==r['sha256'];assert sha(Path(r['source']))==r['source_sha256']
# Source pin chain from deployed-configuration diagnostic build.
pins=json.loads((D.parent/'codex-pv-diag-20261029/source-identity.json').read_text())['checks']
for r in pins:assert sha(S/r['path'])==r['sha256'],r['path']
std=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/std/src')
for f,rel in [('source-fs.rs.txt','fs.rs'),('source-stdio.rs.txt','io/stdio.rs'),('source-io.rs.txt','io/mod.rs'),('source-process.rs.txt','process.rs')]:assert sha(D/f)==sha(std/rel),f
log=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/log-0.4.34/src/lib.rs');assert sha(D/'source-log.rs.txt')==sha(log)
lock=(S/'tools/r1-cost-probe/Cargo.lock').read_text();assert re.search(r'name = "log"\nversion = "0.4.34"',lock)
rows=[]
def row(name,file,start,end,mapping,frontier):
 p=D/file;s=p.read_text();a=s.index(start);b=s.index(end,a)+len(end);body=s[a:b]
 for token,lean in mapping:assert token in body,(name,token)
 rows.append(dict(name=name,source=file,file_sha256=sha(p),body_sha256=hashlib.sha256(body.encode()).hexdigest(),start_line=s[:a].count('\n')+1,end_line=s[:b].count('\n')+1,steps=[dict(rust=a,model=b) for a,b in mapping],unbound=frontier,complete_native_binding=False))
row('Write::write_all','source-io.rs.txt','    fn write_all(&mut self, mut buf:', '\n        Ok(())\n    }',[
 ('while !buf.is_empty()', 'writeAll empty/nonempty split'),('match self.write(buf)', 'write primitive Run'),('Ok(0)', 'writeAll_zero'),('Err(Error::WRITE_ALL_EOF)','IoError.writeZero'),('Ok(n) => buf = &buf[n..]', 'writeAll_progress/oversize'),('Err(ref e) if e.is_interrupted() => {}','writeAll_interrupted and explicit dropInterrupted'),('Err(e) => return Err(e)','writeAll_other_error'),('Ok(())','writeAll_empty')],['write primitive/native syscall, error representation and is_interrupted','ordinary/destructor effects on Interrupted','slicing borrow restoration / panic hook on invalid Write contract','finite fuel is a prefix cut, not proof of native divergence or termination'])
row('fs::write','source-fs.rs.txt','pub fn write<P:', '\n    inner(path.as_ref(), contents.as_ref())\n}',[
 ('File::create(path)?','file_created/file_create_error and abnormal cases'),('.write_all(contents)','writeAll producer call'),('inner(path.as_ref(), contents.as_ref())','AsRef path then contents before inner')],['AsRef conversions and ownership cleanup before/after inner','File::create/OpenOptions backend, Write for File forwarding','File temporary Drop on returned Ok/Err; unwinding on panic/abort','file primitive event readout and actual fd/path association'])
row('stdio::print_to','source-stdio.rs.txt','fn print_to<T>','\nfn print_to_buffer_if_capture_used',[
 ('if print_to_buffer_if_capture_used(args)', 'print_capture_returns/print_fallback'),('return;','ret () after capture'),('if let Err(e) = global_s().write_fmt(args)', 'printGlobal'),('panic!("failed printing to {label}: {e}")','print_error_invokes_hook; complete panic Run')],['OUTPUT_CAPTURE_USED/TLS capture helper, mutex poison recovery, TLS restore/drop','stdout/LineWriter/write_fmt/formatter/global locking, hooks/unwind','source error destructor and native frame association'])
row('attempt_print_to_stderr','source-stdio.rs.txt','pub(crate) fn attempt_print_to_stderr','\n    let _ = stderr().write_fmt(args);\n}',[
 ('if print_to_buffer_if_capture_used(args)', 'stderr_capture_returns/stderr_fallback'),('return;','capture normal return'),('let _ = stderr().write_fmt(args);','ignoreIoError with explicit error Drop')],['complete capture, stderr and Debug formatter calls','io::Error drop body and all abnormal prefixes'])
row('Result::Termination','source-process.rs.txt','impl<T: Termination, E: fmt::Debug> Termination for Result<T, E>', '\n    }\n}',[
 ('match self','report Result split'),('Ok(val) => val.report()','report_ok'),('io::attempt_print_to_stderr(format_args_nl!("Error: {err:?}"));','report_err/debugStderr primitive'),('ExitCode::FAILURE','report_error_failure_exit; returned err Drop explicit')],['E::Debug/anyhow formatter, stderr and destructor body binding','format_args_nl compiler lowering V370','native PCs, panic/OOM, unwind/drop glue'])
plan=S/'tools/r1-cost-probe/src/bin/devnet_spend/plan.rs';main=S/'tools/r1-cost-probe/src/bin/devnet_spend.rs';text=plan.read_text()
ordered=['fs::write(dir.join("proof.bin"),&proof)?','fs::write(dir.join("statement.bin"),public)?','let request=','let hints=','let data=','let page=','let marker=','let mut a=','let stage1_accounts=','if withdrawal{a.extend','a.push(ro(pk(q,"verifier_checkpoint")))','Ok(json!({"client_route"']
a=text.index(ordered[0]);tail=text[a:];pos=[tail.index(x) for x in ordered];assert pos==sorted(pos)
assert 'if q.get("action").is_some(){println!("{}",plan::run(&q)?);return Ok(())}' in main.read_text()
client=dict(plan_sha256=sha(plan),main_sha256=sha(main),tail_order=ordered,model='clientTail/actionMain',unbound=['every intervening post-write call, returned values, allocation/drop/error branch is part of the json tail Run; no claim it is an atomic serialization','all earlier stdin/JSON parsing, recovery dir/file and nonce-store calls','actual native event producer, readout, drop/unwind for every terminal'])
# Public fixture source is recorded, never exported recovery content or keys.
io=[]
for p in [main,plan,S/'crates/aspis-prover/src/state_only_entropy.rs']:
 if not p.exists():continue
 for n,line in enumerate(p.read_text().splitlines(),1):
  if re.search(r'fs::|\.write_all\(|\.sync_all\(|\.read_to_string\(|DurableStateOnlyMaskNonceStore|println!|eprintln!',line):io.append(dict(path=str(p.relative_to(S)),line=n,source=line.strip(),file_sha256=sha(p)))
# Exact dynamic callers, not just the formatting helper.
operands=json.loads((P/'source-bindings.json').read_text())['sites']
logger=log.read_text()
assert 'static mut LOGGER: &dyn Log = &NopLogger;' in logger
assert 'static STATE: AtomicUsize = AtomicUsize::new(0);' in logger
assert 'static MAX_LOG_LEVEL_FILTER: AtomicUsize = AtomicUsize::new(0);' in logger
writes=[]
for n,line in enumerate(logger.splitlines(),1):
 if re.search(r'LOGGER =|STATE\.(store|compare_exchange)|MAX_LOG_LEVEL_FILTER\.store',line):writes.append(dict(line=n,source=line.strip()))
report=dict(source_inputs_checked=len(pins),deployed=dict(toolchain='1.94.1',profile='release',features=['r1p-check','aspis-r1-cost-probe/ct-host-prover'],dependency_lock=dict(path=str(S/'tools/r1-cost-probe/Cargo.lock'),sha256=sha(S/'tools/r1-cost-probe/Cargo.lock')),feature_resolution_authority=str(D.parent/'codex-pv-rdea-20261028/build-source-pins.json')),rows=rows,client=client,io_sites=io,operand_sites=operands,logger=dict(version='0.4.34',sha256=sha(log),initial=dict(STATE=0,MAX_LOG_LEVEL_FILTER=0,LOGGER='NopLogger'),mutations=writes,status='initialization and selection branch identified; exhaustive absence/publicity of every reached setter/constructor/indirect call remains OPEN'),source_control_evidence='own-1 statement association for listed outer control only; not complete transitive source binding',compiler='V370 pending D381/D386 retained',endpoint_premises_removed=0,new_trust=0)
(D/'source-bindings.json').write_text(json.dumps(report,indent=2)+'\n')
print('external checked',len(ext),'project/source cohort checked; source rows',len(rows),'I/O sites',len(io),'whole native links OPEN')
