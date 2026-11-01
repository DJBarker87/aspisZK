"""Instruction-trace comparison of the exact optimized client decoder, plus N7 custody fixtures."""
from pathlib import Path
import ctypes as C,os,signal,subprocess,json,hashlib,re,ast,threading,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');O=H/'final-gates/decoder';O.mkdir(exist_ok=False);B=H/'native-target/client/user_client'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
nm=subprocess.check_output(['nm','-an',B],text=True)
entry=next(l for l in nm.splitlines() if 'decode_wallet_record' in l);offset=int(entry.split()[0],16)
dump=subprocess.check_output(['objdump','-d','-Mintel','--demangle','--start-address='+str(offset),'--stop-address='+str(offset+512),B],text=True)
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
q=json.loads((H.parent/'codex-pv-c474-20261029/runtime-private-final/default/transfer/request.json').read_text())
q.pop('note');q['lane_leaf_sets']=json.loads((H/'fixture-inputs.json').read_text())['lane_leaf_sets']
traces=[]
for label,record in [('zero',bytes(212)),('ff',bytes([255])*212),('ramp',bytes(range(212)))]:
 kr,kw=os.pipe();sr,sw=os.pipe();os.set_inheritable(kr,True)
 os.write(kw,record);os.close(kw);os.write(sw,json.dumps({**q,'wallet_bytes_fd':kr}).encode());os.close(sw)
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
  return_pc=ptr(2,pid,r.rsp)
  maps=[]
  for line in Path(f'/proc/{pid}/maps').read_text().splitlines():
   fields=line.split();lo,hi=[int(v,16) for v in fields[0].split('-')]
   maps.append((lo,hi,int(fields[2],16),fields[-1]))
  def location(pc):
   lo,hi,off,path=next(m for m in maps if m[0]<=pc<m[1]);return dict(module=path,offset=pc-lo+off)
  steps=[]
  for i in range(20000):
   r=regs(pid)
   if r.rip==return_pc:break
   steps.append(dict(pc=location(r.rip),source_pointer_delta=r.rsi-src,destination_pointer_delta=r.rdi-dst))
   ptr(9,pid);wait_trap(pid)
  else:raise AssertionError('decoder trace did not return within 20000 instructions')
  copied=b''.join(ptr(2,pid,dst+i).to_bytes(8,'little') for i in range(0,424,8))[:424]
  expected=record[:64]+record[76:204]+record[64:72]+record[204:212]+record[72:76]+record
  assert copied==expected
  traces.append(dict(secret_class=label,public_shape='212 raw wallet bytes, same public request',steps=steps,copy_correct=True))
 finally:
  os.kill(pid,signal.SIGKILL);os.waitpid(pid,0)
assert all(t['steps']==traces[0]['steps'] for t in traces)
(O/'ct-decoding.json').write_text(json.dumps(dict(evidence_class='instruction-trace comparison',binary_sha256=sha(B),architecture='x86_64 Linux',method='ptrace software breakpoint at decoder entry, PTRACE_SINGLESTEP through RET; instruction PCs including libc tail-copy and RSI/RDI normalized to public entry pointers; output checked against every decoded field and retained record',classes=traces,identical=True,scope='Exact optimized wallet decoder and libc memcpy tail-call; three synthetic 212-byte secret classes of equal public shape. Not dudect, not a whole-loader/signing constant-time proof; V371 CPU latency and I/O/validation obligations retained.'),indent=2)+'\n')
print('WALLET_DECODER_TRACE_PASS',len(traces[0]['steps']),flush=True)
