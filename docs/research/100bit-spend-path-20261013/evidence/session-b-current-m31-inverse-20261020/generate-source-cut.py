from pathlib import Path
import json,shutil,hashlib,subprocess
r=Path('/Users/dominic/ZK');b=Path('/tmp/root-query31-transcript-extraction-v1-20261020');w=Path('/tmp/root-m31-inverse-extraction-v1-20261020');w.mkdir();(w/'input/fragments').mkdir(parents=True);sha=lambda x:hashlib.sha256(x).hexdigest();rev='c8ea8dd49c81ab970b9dbee8d8b47718f9beb005';sp='crates/aspis-core/src/field.rs';source=subprocess.check_output(['git','show',rev+':'+sp],cwd=r).decode()
def cut(marker):
 a=source.index(marker);i=source.index('{',a);n=1;j=i+1
 while n:
  n+=(source[j]=='{')-(source[j]=='}');j+=1
 return source[a:j],a,j
inv,a,z=cut('    pub fn inv(self) -> M31 {');sq,sa,sz=cut('fn square_n(mut value: M31, count: usize) -> M31 {');body='''pub mod field {
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);
'''+sq+'''
impl M31 {
 pub fn mul(self,_:M31)->M31 {unreachable!()}
'''+inv+'\n}\n}\n';(w/'input/lib.rs').write_text(body)
for n in ['Cargo.toml','Cargo.lock']:shutil.copy(b/'input'/n,w/'input'/n)
for n,s in [('m31_inv',inv),('square_n',sq)]: (w/'input/fragments'/(n+'.rs')).write_text(s+'\n')
pins=dict(revision=rev,features=['r0','private-leaf-salts'],root_targets=['crate::field::_::inv'],opaque_paths=['crate::field::_::mul'],cuts=[dict(name='m31_inv',path=sp,start_byte=a,end_byte_exclusive=z,sha256=sha(inv.encode())),dict(name='square_n',path=sp,start_byte=sa,end_byte_exclusive=sz,sha256=sha(sq.encode()))],classification='ACTUAL frozen M31.inv and square_n bodies; explicit M31 multiplication boundary; source-preserving minimal module layout',scope='R17 base-field inverse arithmetic under concrete multiplication semantics; no QueryGeometry Vec or deployed R22 claim',kit_files={n:sha((w/'input'/n).read_bytes()) for n in ['lib.rs','Cargo.toml','Cargo.lock']});(w/'input/source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for n in ['config.json','run-host.py','run-stage.py','run-admitted.py']:shutil.copy(b/n,w/n)
f=w/'config.json';c=json.loads(f.read_text());c['unit']=w.name;c['source_revision']=rev+' exact core M31 inv/square_n, M31.mul opaque boundary';f.write_text(json.dumps(c,indent=2)+'\n');f=w/'run-host.py';f.write_text(f.read_text().replace('AspisR1Query31Transcript','AspisR1M31Inverse'));print(w)
