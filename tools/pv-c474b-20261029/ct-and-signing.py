"""Instruction-trace comparison of the exact optimized client decoder, plus N7 custody fixtures."""
from pathlib import Path
import ctypes as C,os,signal,subprocess,json,hashlib,re,ast,threading,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');O=H/'bundle';B=H/'native-target/client/devnet_spend'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
nm=subprocess.check_output(['nm','-an',B],text=True)
entry=next(l for l in nm.splitlines() if 'decode_raw_key_record' in l);offset=int(entry.split()[0],16)
dump=subprocess.check_output(['objdump','-d','-Mintel','--demangle','--start-address='+str(offset),'--stop-address='+str(offset+96),B],text=True)
instructions=[]
for line in dump.splitlines():
 m=re.match(r'\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s)+)\s*(\S.*)',line)
 if not m:continue
 instructions.append(dict(offset=int(m[1],16)-offset,asm=m[3].strip()))
 if m[3].strip()=='ret':break
assert instructions and instructions[-1]['asm']=='ret'
assert all(i['asm'].split()[0] in ('movups','mov','ret') for i in instructions),instructions
(O/'decoder-disassembly.txt').write_text(dump)
libc=C.CDLL(None,use_errno=True);libc.ptrace.restype=C.c_long
fields='r15 r14 r13 r12 rbp rbx r11 r10 r9 r8 rax rcx rdx rsi rdi orig_rax rip cs eflags rsp ss fs_base gs_base ds es fs gs'.split()
class Regs(C.Structure):_fields_=[(f,C.c_ulonglong) for f in fields]
def ptr(req,pid,addr=0,data=0):
 C.set_errno(0);v=libc.ptrace(C.c_uint(req),C.c_uint(pid),C.c_void_p(addr),data if not isinstance(data,int) else C.c_void_p(data))
 if v==-1 and C.get_errno():raise OSError(C.get_errno(),os.strerror(C.get_errno()))
 return v&((1<<64)-1)
def regs(pid):
 r=Regs();ptr(12,pid,0,C.byref(r));return r
def wait_trap(pid):
 _,s=os.waitpid(pid,0);assert os.WIFSTOPPED(s) and os.WSTOPSIG(s)==signal.SIGTRAP,s
q=dict(keys=['public-shape-placeholder'],key_bytes_fd=0,instructions=[],blockhash='11111111111111111111111111111111')
traces=[]
for label,record in [('zero',bytes(64)),('ff',bytes([255])*64)]:
 kr,kw=os.pipe();sr,sw=os.pipe();os.set_inheritable(kr,True)
 os.write(kw,record);os.close(kw);os.write(sw,json.dumps({**q,'key_bytes_fd':kr}).encode());os.close(sw)
 pid=os.fork()
 if pid==0:
  try:
   os.dup2(sr,0);null=os.open('/dev/null',os.O_RDWR);os.dup2(null,1);os.dup2(null,2)
   ptr(0,0);os.execv(str(B),[str(B)])
  except BaseException:os._exit(127)
 os.close(kr);os.close(sr)
 try:
  wait_trap(pid)
  mapping=next(l for l in Path(f'/proc/{pid}/maps').read_text().splitlines() if str(B) in l and l.split()[2]=='00000000')
  base=int(mapping.split('-')[0],16);at=base+offset;original=ptr(1,pid,at);ptr(4,pid,at,(original&~255)|0xcc)
  ptr(7,pid);wait_trap(pid);r=regs(pid);assert r.rip==at+1
  ptr(4,pid,at,original);r.rip=at;ptr(13,pid,0,C.byref(r));src,dst=r.rsi,r.rdi
  steps=[]
  for instruction in instructions:
   r=regs(pid);assert r.rip-at==instruction['offset']
   steps.append(dict(pc_offset=r.rip-at,instruction=instruction['asm'],source_pointer_delta=r.rsi-src,destination_pointer_delta=r.rdi-dst))
   ptr(9,pid);wait_trap(pid)
  copied=b''.join(ptr(2,pid,dst+i).to_bytes(8,'little') for i in range(0,64,8));assert copied==record
  traces.append(dict(secret_class=label,public_shape='one key, 64 raw bytes, same public request structure',steps=steps,copy_correct=True))
 finally:
  os.kill(pid,signal.SIGKILL);os.waitpid(pid,0)
assert traces[0]['steps']==traces[1]['steps']
(O/'ct-decoding.json').write_text(json.dumps(dict(evidence_class='instruction-trace comparison',binary_sha256=sha(B),architecture='x86_64 Linux',method='ptrace software breakpoint at decoder entry, PTRACE_SINGLESTEP through RET; instruction PCs and memory-base registers normalized to public entry pointers; output checked against class record',classes=traces,identical=True,scope='Exact optimized fixed-copy decoder only; two synthetic 64-byte secret classes of equal public shape. Not dudect, not a whole-loader/signing constant-time proof; V371 CPU latency and I/O/validation obligations retained.'),indent=2)+'\n')
# Exact writer function, excluding driver startup/RPC.
script=H/'src/scripts/r1_devnet_spend.py';node=next(n for n in ast.parse(script.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='invoke')
ns=dict(SIGNER=str(B),json=json,os=os,subprocess=subprocess,threading=threading);exec(compile(ast.Module(body=[node],type_ignores=[]),str(script),'exec'),ns)
seed=bytes.fromhex('9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60');pub=bytes.fromhex('d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a')
key=O/'RFC8032-public-fixture-key.json';assert not key.exists();key.write_text(json.dumps(list(seed+pub)));key.chmod(0o600);before=sha(key)
q=dict(keys=[str(key)],instructions=[],blockhash='11111111111111111111111111111111')
baseline=H/'artifacts/baseline-devnet_spend';assert sha(baseline)=='30d883a8d97f12c315898aaf9170eb7a542b5e935881f089506fd4601ddb6a20'
a=json.loads(subprocess.check_output([baseline],input=json.dumps(q).encode(),timeout=30));b=ns['invoke'](q);assert a==b and before==sha(key)
(O/'signing-fixture.json').write_text(json.dumps(dict(byte_identical=True,transaction_bytes=a['bytes'],transaction_sha256=hashlib.sha256(bytes.fromhex(a['hex'])).hexdigest(),fixture='RFC8032 public unfunded vector 1; no RPC, retained mode 0600',key_unchanged=True,baseline_sha256=sha(baseline),client_sha256=sha(B)),indent=2)+'\n')
errors=[]
for label,data in [('short',bytes(63)),('extra',seed+pub+b'\0')]:
 rfd,wfd=os.pipe();os.write(wfd,data);os.close(wfd)
 r=subprocess.run([B],input=json.dumps({**q,'key_bytes_fd':rfd}),text=True,capture_output=True,pass_fds=(rfd,),timeout=30);os.close(rfd)
 assert r.returncode==1 and r.stderr=='client error\n';errors.append(dict(case=label,exit=r.returncode,stderr=r.stderr))
for label,data in [('malformed',b'not JSON'),('panic',b'{}')]:
 r=subprocess.run([B],input=data,capture_output=True,env=dict(os.environ,RUST_BACKTRACE='full',RUST_LIB_BACKTRACE='1'))
 assert not r.stdout and r.stderr==(b'client error\n' if label=='malformed' else b'client panic\n')
 errors.append(dict(case=label,exit=r.returncode,stderr=r.stderr.decode()))
(O/'shape-and-diagnostic-errors.json').write_text(json.dumps(errors,indent=2)+'\n')
print('CT_INSTRUCTION_TRACE_SIGNING_SHAPE_DIAGNOSTIC_PASS',flush=True)
