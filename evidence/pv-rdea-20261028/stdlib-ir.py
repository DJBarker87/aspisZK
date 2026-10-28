from pathlib import Path
import ctypes as C,subprocess,json,hashlib,lzma,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu')
O=D/'stdlib-ir';O.mkdir(exist_ok=True)
lib=C.CDLL(str(R/'lib/libLLVM.so.21.1-rust-1.94.1-stable'))
lib.LLVMContextCreate.restype=C.c_void_p
lib.LLVMCreateMemoryBufferWithContentsOfFile.argtypes=[C.c_char_p,C.POINTER(C.c_void_p),C.POINTER(C.c_char_p)]
lib.LLVMParseBitcodeInContext2.argtypes=[C.c_void_p,C.c_void_p,C.POINTER(C.c_void_p)]
lib.LLVMPrintModuleToString.argtypes=[C.c_void_p];lib.LLVMPrintModuleToString.restype=C.c_void_p
lib.LLVMDisposeMessage.argtypes=[C.c_void_p];lib.LLVMDisposeModule.argtypes=[C.c_void_p];lib.LLVMContextDispose.argtypes=[C.c_void_p];lib.LLVMDisposeMemoryBuffer.argtypes=[C.c_void_p]
rows=[]
for crate in ['std','alloc']:
 archive=next((R/'lib/rustlib/x86_64-unknown-linux-gnu/lib').glob('lib'+crate+'-*.rlib'))
 for member in subprocess.check_output(['ar','t',str(archive)],text=True).splitlines():
  if not member.endswith('.o'):continue
  p=O/member;p.write_bytes(subprocess.check_output(['ar','p',str(archive),member]))
  sections=subprocess.check_output(['readelf','-SW',str(p)],text=True)
  row=dict(crate=crate,archive=str(archive),archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),member=member,object_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),sections=sections)
  bc=p.with_suffix('.bc')
  if '.llvmbc' not in sections:
   row['embedded_bitcode']=False;rows.append(row);continue
  subprocess.run(['objcopy','--dump-section','.llvmbc='+str(bc),str(p)],check=True)
  row.update(embedded_bitcode=True,bitcode_sha256=hashlib.sha256(bc.read_bytes()).hexdigest(),bitcode_bytes=bc.stat().st_size)
  ctx=lib.LLVMContextCreate();buf=C.c_void_p();err=C.c_char_p();mod=C.c_void_p()
  assert lib.LLVMCreateMemoryBufferWithContentsOfFile(str(bc).encode(),C.byref(buf),C.byref(err))==0,err.value
  assert lib.LLVMParseBitcodeInContext2(ctx,buf,C.byref(mod))==0
  ptr=lib.LLVMPrintModuleToString(mod);data=C.string_at(ptr)
  out=O/(crate+'.ll.xz');out.write_bytes(lzma.compress(data,preset=6))
  row.update(ir_file=str(out),ir_sha256=hashlib.sha256(data).hexdigest(),ir_bytes=len(data),debug_locations=data.count(b'!DILocation'),String_capacity_mentions=data.count(b'with_capacity'))
  lib.LLVMDisposeMessage(ptr);lib.LLVMDisposeModule(mod);lib.LLVMDisposeMemoryBuffer(buf);lib.LLVMContextDispose(ctx)
  rows.append(row)
(D/'stdlib-ir.json').write_text(json.dumps(dict(toolchain='rustc1.94.1 installed release sysroot; read-only archive analysis',llvm=str(R/'lib/libLLVM.so.21.1-rust-1.94.1-stable'),rows=rows),indent=2)+'\n')
print(json.dumps([{k:r.get(k) for k in ['crate','embedded_bitcode','ir_bytes','debug_locations','String_capacity_mentions']} for r in rows]))
