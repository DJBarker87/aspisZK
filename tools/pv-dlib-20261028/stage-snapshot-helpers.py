"""Append proof-only valid-state constructors; preserve all native prefixes."""
from pathlib import Path
import subprocess,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';H='dombarker@100.108.41.90'
g='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
r=subprocess.run(['ssh',H,f'mkdir -p {D}/stage-snapshot; python3 {g}/reservation.py {D}/stage-snapshot/admission.json > {D}/stage-snapshot/reservation.log 2>&1'])
a=subprocess.check_output(['ssh',H,f'cat {D}/stage-snapshot/admission.json'],text=True);(E/'stage-snapshot-admission.json').write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:raise SystemExit(78)
code='''from pathlib import Path
b=Path(DIR)
p=b/'native/block-buffer-0.10.4/src/lib.rs';s=p.read_text();assert 'pv_dl_from_snapshot' not in s
s+='''+repr('''
#[cfg(kani)] impl BlockBuffer<generic_array::typenum::U64,Eager> {
    pub fn pv_dl_from_snapshot(bytes:[u8;64],pos:u8)->Self {
        assert!(pos<64);
        Self {buffer:GenericArray::clone_from_slice(&bytes),pos,_pd:PhantomData}
    }
}
''')+'''
p.write_text(s)
p=b/'native/digest-0.10.7/src/core_api/wrapper.rs';s=p.read_text();assert 'pv_dl_from_parts' not in s
s+='''+repr('''
#[cfg(kani)] impl<T> CoreWrapper<T>
where T:BufferKindUser,T::BlockSize:IsLess<U256>,Le<T::BlockSize,U256>:NonZero {
    pub fn pv_dl_from_parts(core:T,buffer:Buffer<T>)->Self {Self{core,buffer}}
}
''')+'''
p.write_text(s)
print('proof constructors appended; no original body changed')
'''
code=code.replace('DIR',repr(D));r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);print(r.stdout,r.stderr);assert r.returncode==0
for f in ['native-default.rs','default-reference.rs','update-gate.rs','padding-gate.rs']:
 subprocess.run(['scp',str(R/'tools/pv-dlib-20261028'/f),H+':'+D+'/native-proof/'+f],check=True)
subprocess.run(['scp',str(R/'tools/pv-dlib-20261028/default-reference.rs'),H+':'+D+'/reference/default-reference.rs'],check=True)
