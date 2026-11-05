"""Strict cfg(false) erasure check for the strengthened tree0 control hooks."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
name='sources/NIL_src/crates/aspis-r1-cost-probe/src/NIL_tree_native.rs'
a=(E/'NIL_K021'/name).read_text();b=(E/'NIL_K022'/name).read_text()
a1=a.replace('let result=step','let mut result=step').replace('assert!(if cfg!(NIL_invert){!good}else{good});','assert!(good);')
b1=re.sub(r'^ if cfg!\(NIL_invert\)\{match C\{[^\n]*\n','',b,flags=re.M)
assert a1!=a and b1!=b
clean=lambda s:re.sub(r'\s+','',s)
assert clean(a1)==clean(b1),'changed positive behavior beyond dead control/mutability annotation'
x={'status':'PASS','positive':'NIL_K021','control':'NIL_K022','source_sha256':hashlib.sha256(a.encode()).hexdigest(),'control_source_sha256':hashlib.sha256(b.encode()).hexdigest(),'cfg_false_erasure_sha256':hashlib.sha256(clean(a1).encode()).hexdigest(),'changes':'new control hook erased under cfg(false); let mut annotation; previous predicate inversion simplified at false. Actual step and asserted positive predicate unchanged.'}
(E/'NIL_CONTROL_ERASURE.json').write_text(json.dumps(x,indent=2)+'\n')
if __name__=='__main__':print(json.dumps(x))
