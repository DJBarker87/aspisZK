from pathlib import Path
import re,hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028';p=E/'box-lowering.ll.txt';s=p.read_text()
assert len(re.findall(r'__rust_alloc\(i64 noundef 2116, i64 noundef range\([^\n]*\) 4\)',s))==1
assert 'alloca [2112 x i8], align 4' in s
for n in [1600,480,32]:assert re.search(r'@llvm.memcpy[^\n]*i64 '+str(n)+r', i1 false\)',s)
alloc=s.index('__rust_alloc(i64');branch=s.index('icmp eq ptr %0, null');handler=s.index('handle_alloc_error17');copy=s.index('dereferenceable(2112) %0');variant=s.index('store i8 %variant');returned=s.index('ret ptr %0')
assert alloc<branch<handler<copy<variant<returned
assert 'i64 noundef 4, i64 noundef 2116' in s[handler:copy]
assert 'getelementptr inbounds nuw i8, ptr %0, i64 2112' in s
assert 1600+480+32==2112 and 2112+1+3==2116
j=dict(status='PASS',artifact=str(p.relative_to(E)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),stack_temporary=dict(size=2112,alignment=4),heap_requests=[dict(size=2116,alignment=4,order=0)],reallocations=[],failure='null -> handle_alloc_error -> unreachable; no heap initialization or returned Box',error_handler_llvm_abi_arguments=[4,2116],success='copy 2112 initialized payload bytes then store variant byte at offset2112; return pointer',padding='three padding bytes are not claimed initialized',intrinsic_binding='deployed 1.94.1 release LLVM, same frozen weights source; memcpy/native compiler semantics remain reclassification within existing tool trust, never a Kani premise-removal claim',law='PV_RDB2C_Box.complete/initialized; BoxAdequacy.initialized_fresh_aligned; PrimitiveResults.boxed_complete/boxed_with_handlers',retained='runtime/allocator primitive adequacy including null result, private state, freshness, alignment and actual error handler; compiler cohort D381/D386; L1/L2/L3 unchanged')
(E/'box-lowering-binding.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j,indent=2))
