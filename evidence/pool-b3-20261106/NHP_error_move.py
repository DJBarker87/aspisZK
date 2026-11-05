"""Reach the actual std residual/FromSame path on every SDK-word-produced error."""
from pathlib import Path
import subprocess,sys,json,difflib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
r=subprocess.run([sys.executable,str(E/'NHP_error_word.py'),'positive'],capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads((E/'NHP_CURRENT.json').read_text());s=x['source']
s=s.replace('let returned=ProgramError::from(word);','''let returned=ProgramError::from(word);
 let query:usize=kani::any();kani::assume(query<7);
 let allocation=match &returned {ProgramError::BorshIoError(text)=>Some((text.as_ptr(),text.len(),text.as_bytes()[query])),_=>None};
 let propagated=(||->Result<(),ProgramError>{Err::<(),ProgramError>(returned)?;Ok(())})();
 let returned=propagated.err().unwrap();''')
s=s.replace('ProgramError::BorshIoError(text)=>{let bytes=', '''ProgramError::BorshIoError(text)=>{let saved=allocation.unwrap();assert!(text.as_ptr()POINTERsaved.0);assert!(text.len()==saved.1);assert!(text.as_bytes()[query]==saved.2);let bytes=''').replace('POINTER','==' if mode=='positive' else '!=')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';p='programs/aspis-pool/src/error.rs';before=subprocess.check_output(['git','show',rev+':'+p],text=True);after=before+'\n#[cfg(kani)]\nmod NHP_ErrorWord {\n'+s+'}\n'
patch=(E/'NHP_native.patch').read_text();start=patch.index('--- a/programs/aspis-pool/src/lib.rs');tail=patch[start:]
patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+tail
(E/'NHP_native.patch').write_text(patch);x.update(kind='SDK word error actual residual move',mode=mode,source=s,domain='Every SDK From<u64> producer error; all26 constructors, full Custom payload and Borsh Unknown allocation pointer/length/arbitrary byte through actual Rust ?/FromSame',remaining='general arbitrary-String native frame and caller proof of SDK-word-origin domain; no composed credit');(E/'NHP_CURRENT.json').write_text(json.dumps(x,indent=1)+'\n')
print('error::NHP_ErrorWord::association')
