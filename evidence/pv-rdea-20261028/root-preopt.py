from pathlib import Path
import subprocess,json,os,hashlib,shutil,ctypes as C,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');S=D.parent/'codex-pv-fscan-20261028/src';R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu')
B=D/'client-target/release/devnet_spend';baseline=D/'client-deployed-baseline'
expected=json.loads((D/'client-artifact.json').read_text())['sha256']
assert hashlib.sha256(B.read_bytes()).hexdigest()==expected
if baseline.exists():assert hashlib.sha256(baseline.read_bytes()).hexdigest()==expected
else:shutil.copyfile(B,baseline)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',RUSTC_BOOTSTRAP='1',CARGO_TARGET_DIR=str(D/'client-target'),RUSTC_WRAPPER=str(D/'emit-wrapper.py'))
cmd=['taskset','--cpu-list','0-3','cargo','rustc','--release','--locked','--manifest-path',str(S/'tools/r1-cost-probe/Cargo.toml'),'-p','aspis-r1-cu-probe','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','devnet_spend','-j','4','--','-Csave-temps']
(D/'root-preopt-command.json').write_text(json.dumps(dict(command=cmd,phase='re-emit only root with save-temps; profile/features/toolchain unchanged; missing pre-optimization bitcode is the new evidence artifact',original_binary_sha256=expected),indent=2)+'\n')
subprocess.run(cmd,env=env,check=True)
lib=C.CDLL(str(R/'lib/libLLVM.so.21.1-rust-1.94.1-stable'));lib.LLVMContextCreate.restype=C.c_void_p
lib.LLVMCreateMemoryBufferWithContentsOfFile.argtypes=[C.c_char_p,C.POINTER(C.c_void_p),C.POINTER(C.c_char_p)]
lib.LLVMParseBitcodeInContext2.argtypes=[C.c_void_p,C.c_void_p,C.POINTER(C.c_void_p)]
lib.LLVMPrintModuleToString.argtypes=[C.c_void_p];lib.LLVMPrintModuleToString.restype=C.c_void_p
lib.LLVMDisposeMessage.argtypes=[C.c_void_p];lib.LLVMDisposeModule.argtypes=[C.c_void_p];lib.LLVMContextDispose.argtypes=[C.c_void_p];lib.LLVMDisposeMemoryBuffer.argtypes=[C.c_void_p]
O=D/'root-preopt';O.mkdir(exist_ok=True);rows=[]
files=sorted((D/'client-target').rglob('devnet_spend*.no-opt.bc'));assert files,'No pre-optimization bitcode emitted'
for idx,p in enumerate(files):
 ctx=lib.LLVMContextCreate();buf=C.c_void_p();err=C.c_char_p();mod=C.c_void_p()
 assert lib.LLVMCreateMemoryBufferWithContentsOfFile(str(p).encode(),C.byref(buf),C.byref(err))==0,err.value
 assert lib.LLVMParseBitcodeInContext2(ctx,buf,C.byref(mod))==0
 ptr=lib.LLVMPrintModuleToString(mod);data=C.string_at(ptr);out=O/(str(idx)+'.ll.xz');out.write_bytes(lzma.compress(data,preset=6))
 rows.append(dict(bitcode=str(p),bitcode_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),ir=str(out),ir_sha256=hashlib.sha256(data).hexdigest(),ir_bytes=len(data)))
 lib.LLVMDisposeMessage(ptr);lib.LLVMDisposeModule(mod);lib.LLVMDisposeMemoryBuffer(buf);lib.LLVMContextDispose(ctx)
(D/'root-preopt.json').write_text(json.dumps(dict(command=cmd,rows=rows,baseline_sha256=expected,diagnostic_binary_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),same_binary=hashlib.sha256(B.read_bytes()).hexdigest()==expected),indent=2)+'\n')
print('preopt modules',len(rows),'same binary',hashlib.sha256(B.read_bytes()).hexdigest()==expected)
