"""Finite native startup/FD gates; no prover call and no timing experiment."""
from pathlib import Path
import json,os,subprocess,time,hashlib,signal
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');O=H/'final-gates/uc5/runtime';O.mkdir()
client=H/'native-target/client/user_client'
helper=H/'uc5-startup.rs'
helper.write_text('''#[path="src/tools/r1-cost-probe/src/bin/user_client/diagnostics.rs"] mod diagnostics;
unsafe extern "C" { fn prctl(option:i32,...) -> i32; fn getrlimit(resource:u32,limit:*mut [u64;2])->i32; }
fn main(){diagnostics::initialize();let mut core=[1u64;2];assert_eq!(unsafe{getrlimit(4,&mut core)},0);println!("dumpable={} core={},{}",unsafe{prctl(3)},core[0],core[1]);print!("{}",std::fs::read_to_string("/proc/self/status").unwrap());panic!("forced private panic payload");}
''')
cmd=['/home/dombarker/.cargo/bin/rustc','+1.94.1','--edition=2021','-C','opt-level=3','-C','panic=abort',str(helper),'-o',str(H/'uc5-startup')]
subprocess.run(cmd,cwd=H,check=True,capture_output=True)
r=subprocess.run([str(H/'uc5-startup')],cwd=O,capture_output=True)
(O/'helper-stdout.txt').write_bytes(r.stdout);(O/'helper-stderr.txt').write_bytes(r.stderr)
assert r.returncode==-signal.SIGABRT and r.stdout.startswith(b'dumpable=0 core=0,0\n') and r.stderr==b'client panic\n'
# The actual final ELF is stopped on public stdin after initialize; then force
# a panic with a missing public key. Trace only public hardening syscalls.
p=subprocess.Popen(['strace','-qq','-e','trace=prctl,setrlimit,prlimit64','-o',str(O/'startup-syscalls.txt'),str(client)],cwd=O,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
# strace is the parent; locate the traced client before sending the request.
child=None
for _ in range(100):
 children=Path(f'/proc/{p.pid}/task/{p.pid}/children').read_text().split()
 if children:
  candidate=int(children[0]);status=Path(f'/proc/{candidate}/status').read_text()
  if 'user_client' in status:
   trace=(O/'startup-syscalls.txt').read_text()
   if 'PR_SET_DUMPABLE, SUID_DUMP_DISABLE) = 0' in trace or 'PR_SET_DUMPABLE, 0) = 0' in trace:child=candidate;break
 time.sleep(.02)
assert child is not None
status=Path(f'/proc/{child}/status').read_text();limits=Path(f'/proc/{child}/limits').read_text();(O/'client-status.txt').write_text(status);(O/'client-limits.txt').write_text(limits)
out,err=p.communicate(b'{"action":"prove"}',timeout=10)
(O/'client-stdout.txt').write_bytes(out);(O/'client-stderr.txt').write_bytes(err)
assert err==b'client panic\n' and p.returncode!=0 and not out
trace=(O/'startup-syscalls.txt').read_text();assert 'RLIMIT_CORE' in trace and 'rlim_cur=0, rlim_max=0' in trace
assert not list(O.glob('core*'))
# Native rejection controls and a forced panic after the fixture wallet was read.
F=json.loads((H/'fixture-inputs.json').read_text())
control=H.parent/'codex-pv-c474-20261029/runtime-private-final/default/transfer/request.json'
base=json.loads(control.read_text());base.pop('note');base.update(lane_leaf_sets=F['lane_leaf_sets'],withdrawal_amount=250,proof_dir=str(O/'never-created'))
controls=[]
for case in ['stdio','same-input','regular-file','read-only','after-secret-panic']:
 q=dict(base);rfd,wfd=os.pipe();record=bytes.fromhex(F['records'][0]);os.write(wfd,record);os.close(wfd);q['wallet_bytes_fd']=rfd
 outread,outwrite=os.pipe();extra=None
 if case=='stdio':fd=1
 elif case=='same-input':fd=rfd
 elif case=='regular-file':extra=os.open(O/'empty-control-file',os.O_CREAT|os.O_WRONLY,0o600);fd=extra
 elif case=='read-only':fd=outread
 else:fd=outwrite;q['lane_bytes']='0'
 q['wallet_output_fd']=fd
 inherited=tuple(set([rfd,outwrite,outread]+([] if extra is None else [extra])))
 result=subprocess.run([str(client)],input=json.dumps(q).encode(),capture_output=True,pass_fds=inherited,cwd=O)
 for channel in inherited:os.close(channel)
 assert result.stdout==b'' and result.stderr==(b'client panic\n' if case=='after-secret-panic' else b'client error\n')
 assert result.returncode==(-signal.SIGABRT if case=='after-secret-panic' else 1)
 controls.append(dict(case=case,exit=result.returncode,stdout_bytes=0,stderr_literal=True))
assert not (O/'never-created').exists() and (O/'empty-control-file').stat().st_size==0
assert not list(O.glob('core*'))
assert 'core dumped' not in trace
(O/'core-pattern.txt').write_text(Path('/proc/sys/kernel/core_pattern').read_text())
row=dict(evidence_class='finite native source-bound startup and final-ELF forced-panic gate',client_sha256=hashlib.sha256(client.read_bytes()).hexdigest(),forced_panic=True,no_core_file=True,fd_controls=controls,post_secret_panic_no_core=True,helper_dumpable=0,helper_core=[0,0],helper_build=cmd,helper_source_sha256=hashlib.sha256(helper.read_bytes()).hexdigest(),proc_status_dumpable_field_present='Dumpable:' in status,proc_status_core_dumping='CoreDumping:\t0' in status,limitation='Linux 6.8 /proc status omits Dumpable; PR_GET_DUMPABLE in source-identical initialize helper and final-ELF successful PR_SET_DUMPABLE trace establish setting; CoreDumping alone does not')
(O/'summary.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row))
