from pathlib import Path
import subprocess,json,lzma,base64,hashlib
E=Path(__file__).resolve().parent;REV='d0fb4b26f363a1ecf18275de40afb72d7a843adc';sha=lambda b:hashlib.sha256(b).hexdigest()
remote='''from pathlib import Path
import hashlib,json,base64
b=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028')
r=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
pins=json.loads((b/'native-prefix-pins.json').read_text());out={}
for x in pins:
 p=r/x['crate']/x['relative_path'];raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==x['sha256'],str(p)
 out['native/'+x['crate']+'/'+x['relative_path']]=base64.b64encode(raw).decode()
# Current lock is read-only: compare version/manifest dependency pins before use.
out['native-proof/Cargo.lock']=base64.b64encode((b/'native-proof/Cargo.lock').read_bytes()).decode()
print(json.dumps({'pins':pins,'files':out}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=remote,text=True,capture_output=True);assert r.returncode==0,r.stderr;d=json.loads(r.stdout);files={n:base64.b64decode(b)for n,b in d['files'].items()}
def git(p):return subprocess.check_output(['git','show',REV+':tools/pv-dlib-20261028/'+p])
files['native-proof/Cargo.toml']=git('NativeCargo.toml.txt')+b'\n[features]\nnegative-padding=[]\n'
files['native-proof/default-reference.rs']=git('default-reference.rs')
files['native-proof/native-default.rs']=b'#[path="default-reference.rs"] mod reference;\n#[cfg(kani)] #[path="padding-coordinate.rs"] mod padding_coordinate_gate;\n'
t=git('padding-coordinate.rs').decode();old='assert_eq!(count,rc);';assert t.count(old)==1;t=t.replace(old,'if cfg!(feature="negative-padding") { assert_ne!(count,rc); } else { '+old+' }');files['native-proof/padding-coordinate.rs']=t.encode()
helper=b'''\n#[cfg(kani)] impl BlockBuffer<generic_array::typenum::U64,Eager> {
    pub fn pv_dl_from_snapshot(bytes:[u8;64],pos:u8)->Self {
        assert!(pos<64);
        Self {buffer:GenericArray::clone_from_slice(&bytes),pos,_pd:PhantomData}
    }
}
'''
files['native/block-buffer-0.10.4/src/lib.rs']+=helper
raw=json.dumps({n:base64.b64encode(b).decode()for n,b in files.items()}).encode();(E/'Padding-source.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'Padding-source.json.sha256').write_text(sha(raw)+'\n')
(E/'PADDING-SOURCE-CLOSURE.json').write_text(json.dumps({'credit':'C052','receipt_source_revision':REV,'native_prefix_pins':d['pins'],'original_harness_sha256':sha(git('padding-coordinate.rs')),'original_constructor_script':REV+':tools/pv-dlib-20261028/stage-snapshot-helpers.py','root_selection':'Only selected padding_coordinate_gate and its complete original reference; unrelated default/update harnesses excluded. Original native len64_padding_be unchanged. All callback events already local in the original. Same module/function/unwind70/raw64/pos<64/bit_len/event/byte domains.','control':'First count==reference-count assertion inverted, all other assertions unchanged','unrestored_native_logs':['C053 generic_default_gate::wrapper_default_arbitrary_core: DEFAULT_STATE is read inside native Default::default; no local record can seed that parameterless trait method with the same association','C051 empty_gate::empty_noncopy_length_branches: DROPS written inside native Token::drop'], 'transfer':'K-1 and new reached std parity remain separate; does not establish whole SHA/finalizer/native backend.'},indent=2)+'\n')
print(len(files),'verified original dependency files and selected harness/reference')
