from pathlib import Path
import subprocess,json,difflib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-front3-20261028';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
files={};patch=[]
for name in ['candidate','r1_wire','verifier','compact','lib']:
 p='crates/aspis-r1-cost-probe/src/'+name+'.rs';old=subprocess.check_output(['git','show',F+':'+p],text=True);s=old
 if name=='lib':s='#![cfg_attr(kani, feature(allocator_api))]\n'+s+'\n#[cfg(kani)] mod NDF_controls;\n'
 if name=='candidate':
  for fn,req,expr in [('opening','proof.len()==compact::PROOF_BYTES && i<22','r.as_ptr() == NDF_candidate::reference::opening_ref(proof,i).as_ptr() && r.len() == 832'),('batch_key_at','index<16','*r == NDF_candidate::reference::batch_key_at_ref(keys,index)'),('same_batch_index','index<16','*r == NDF_candidate::reference::same_batch_index_ref(values,index,expected)'),('same_batch_leaf','index<16','*r == NDF_candidate::reference::same_batch_leaf_ref(values,index,leaf)')]:
   s=s.replace('fn '+fn+'(',f'#[cfg_attr(kani, kani::requires({req}))]\n#[cfg_attr(kani, kani::ensures(|r| ({expr}) != cfg!(NDF_invert_{fn})))]\nfn '+fn+'(')
  s+='\n#[cfg(kani)] #[path="NDF_candidate.rs"] mod NDF_candidate;\n'
 if name=='r1_wire':
  s=s.replace('pub(crate) fn row(&self)', '#[cfg_attr(kani, kani::ensures(|r| (*r == NDF_wire::reference::validated_row_ref(self.row)) != cfg!(NDF_invert_row)))]\n    pub(crate) fn row(&self)')
  s=s.replace('pub fn state(&self)', '#[cfg_attr(kani, kani::ensures(|r| (*r == NDF_wire::reference::state_ref(self.state)) != cfg!(NDF_invert_state)))]\n    pub fn state(&self)')
  s=s.replace("pub(crate) fn framed(&self)", '#[cfg_attr(kani, kani::ensures(|r| (r.as_ptr()==self.framed.as_ptr() && r.len()==self.framed.len()) != cfg!(NDF_invert_framed)))]\n    pub(crate) fn framed(&self)')
  s+='\n#[cfg(kani)] #[path="NDF_wire.rs"] mod NDF_wire;\n'
 files[p]=s;patch+=list(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NDF_instrument.patch').write_text(''.join(patch))
code='''from pathlib import Path
import json,hashlib
b=Path(B);s=b/'NDF_src';files=json.loads(PAYLOAD)
for n,v in files.items():
 p=s/n
 if p.is_symlink():p.unlink()
 p.write_text(v)
pins={str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}
(b/'NDF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(dict(files=pins)))
'''.replace('PAYLOAD',repr(json.dumps(files))).replace('Path(B)','Path('+repr(B)+')')
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);(E/'NDF_PREPARE.json').write_text(r.stdout);assert r.returncode==0,r.stderr
