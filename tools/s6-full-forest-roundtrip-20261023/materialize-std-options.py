#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys
from generated_syntax import clean
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021/s6-std-options-extraction';S=B/'lean-candidates/s126-caller-boundary-20261021'
x=json.loads((E/'source/Std.llbc').read_text());t=next(t for t in x['translated']['type_decls'] if t and t['item_meta']['name']==[{'Ident':['core',0]},{'Ident':['option',0]},{'Ident':['Option',0]}])
assert [(v['name'],v['discriminant']['Scalar']['Signed']) for v in t['kind']['Enum']]==[('None',['Isize','0']),('Some',['Isize','1'])]
assert not list((E/'source/generated').rglob('*External*'))
raw=E/'source/generated/AspisS6StdOptionMethods/Funs.lean';s='import Aeneas\nset_option autoImplicit false\n'+clean(raw.read_text())
s=s.replace('namespace AspisS6StdOptionMethods',"""namespace AspisS6StdOptionMethods
/-- Exact discriminants from the included current Rust Option LLBC declaration.
The backend uses Lean Option but omits this required generated instance. -/
instance optionDiscriminant {T : Type} : Discriminant (Option T) Isize where
  read_discriminant
    | none => 0#isize
    | some _ => 1#isize
""",1)
s+='\n#print axioms AspisS6StdOptionMethods.option_ok_or\n#print axioms AspisS6StdOptionMethods.option_eq\n'
p=S/'S6StdOptionSourceV1.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
m=json.loads((E/'materialization.json').read_text());assert m['source_sha256']==hashlib.sha256(s.encode()).hexdigest();assert m['raw_funs_sha256']==hashlib.sha256(raw.read_bytes()).hexdigest()
