from pathlib import Path
import subprocess,sys,json,difflib
E=Path(__file__).resolve().parent
r=subprocess.run([sys.executable,str(E/'NHP_metadata.py'),'positive','payer-alias'],capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads((E/'NHP_CURRENT.json').read_text());assert x['source']==json.loads((E/'NHP_K096-shape.json').read_text())['source']
s=x['source'].replace('assert!((alloc::rc::Rc::as_ptr','a1.data.borrow_mut()[0]^=1;\nassert!((alloc::rc::Rc::as_ptr',1)
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';p='programs/aspis-pool/src/processor.rs';before=subprocess.check_output(['git','show',rev+':'+p],text=True);after=before+'\n#[cfg(kani)]\nmod NHP_metadata {\n'+s+'}\n'
current=(E/'NHP_native.patch').read_text();tail=current[current.index('--- a/programs/aspis-pool/src/lib.rs'):]
(E/'NHP_native.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+tail)
x.update(kind='payer alias explicit frame-corruption control',mode='negative',source=s,paired_positive='NHP_K096',remaining='negative evidence control only; source function is not blamed for deliberate harness mutation');(E/'NHP_CURRENT.json').write_text(json.dumps(x,indent=1)+'\n')
print('processor::NHP_metadata::association')
