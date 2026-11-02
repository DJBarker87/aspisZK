"""Audit local raw-frame laws and their native error consumer; no closure claim."""
from pathlib import Path
import json,hashlib,re,sys
E=Path('evidence/pv-evh10-20261102')
modules=['LinuxRawBounds','LinuxRawSpatial','LinuxRawFrame','LinuxRawHistoryTrace','LinuxRawThreaded','StackEntropyFrame','NativeEntropyMemory','NativeRawSpatial','NativeRawReceipt']
rows=[]
for name in modules:
 p=Path('lean/PV_EVH_'+name+'.lean');raw=p.read_bytes();text=raw.decode()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s',text,re.M)
 laws=re.findall(r'^theorem (\w+)',text,re.M)
 assert set(laws)==set(re.findall(r'^#print axioms (\w+)',text,re.M))
 accepted=[json.load(open(q)) for q in E.glob('receipt-*.json') if json.load(open(q)).get('accepted') and json.load(open(q)).get('target')=='PV_EVH_'+name]
 assert len(accepted)==1,(name,'not uniquely accepted')
 r=accepted[0];assert r['source_sha256']==hashlib.sha256(raw).hexdigest()
 rows.append(dict(module='PV_EVH_'+name,source_sha256=r['source_sha256'],attempt=r['attempt'],laws=laws))
s=Path('lean/PV_EVH_NativeRawReceipt.lean').read_text()
for t in ['opsNative (rawBase base)','HeapSeparate slot w','LiveSeparate slot w','HeapCoherent w','history.delivery.status','Threaded initial','history.calls.flatMap','error_live_memory']:assert t in s
out=dict(evidence_class='checked local control/frame/history laws connected to the actual extracted entropy-error branch at opsNative',
 modules=rows,
 discharged=['Every begun raw request is a suffix of original64; every requested byte is in that interval, on all outcomes/prefixes','Per-request heap/live separation follows from original admission, rather than separate retry frame assumptions','Private call buffers and OS worlds are continuous into the final delivery','Every delivery event is accounted for by ordered existing per-call events; no private byte payload invented','Initializer/fill/deployed zeroize1.9.0 cleanup preserve all old LIVE stack bytes','Consumed prefix preservation follows from per-syscall footprint, with that footprint explicitly P'],
 retained=['original physical address/source/native frame association and heap/live spatial separation','initial coherent heap and actual allocator ownership','KernelFrame syscall-memory obligation; actual x86_64 raw ABI/kernel association','successful entropy continuation inner32 lifetimes and retry/drop path','advancing-world residual family and all seven callback installations/full entry','allocator ValidAnswer/native metadata/System binding and literal diagnostic writer/hook/drop fidelity','L3 joint observation and V370/V371; no changes to V221/V222 deployed law','actual-family oraclePrefix/countTrace/nonce-store fileTrace and actual success nonemptiness under v-prime'],
 trust_fields_added=[],rows_removed=[],release_replay=False)
p=E/'getrandom-frame-laws.json'
if '--check' in sys.argv:assert json.load(open(p))==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS local raw-frame/native-error laws; original provenance/kernel/full-entry/L3 obligations retained')
