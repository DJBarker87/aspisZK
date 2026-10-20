#!/usr/bin/env python3
from pathlib import Path
import argparse,re,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();t=Path(__file__).resolve().parent;area=t.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(t/'geometry-candidate7-generated/Types.lean').read_text();fixed=raw
for name in ['r0.Error','verifier.Error']:
 pattern=r'@\[discriminant isize\]\ninductive '+re.escape(name)+r' where\n((?:\|[^\n]+\n)+)'
 m=re.search(pattern,fixed);assert m,name
 cases=re.findall(r'^\| (\w+) :',m[1],re.M);new='inductive '+name+' where\n'+m[1]+'\ndef '+name+'.read_discriminant : '+name+' → Isize\n'+''.join('  | .'+tag+' => '+str(i)+'#isize\n'for i,tag in enumerate(cases))+'\ninstance _root_.AspisR1GeometryCandidate7.'+name+'.instDiscriminant :\n    Discriminant '+name+' Isize where\n  read_discriminant := '+name+'.read_discriminant\n'
 fixed=fixed[:m.start()]+new+fixed[m.end():]
rawfuns=(t/'geometry-candidate7-generated/Funs.lean').read_bytes()
files={'Types.lean':fixed.encode(),'Funs.lean':re.sub(rb'toStr ("[^"]*")',rb'toStr \1 (by norm_num [U32.max,U32.numBits,UScalar.max,UScalarTy.numBits]; decide)',(t/'geometry-candidate7-generated/Funs.lean').read_bytes())}
legacy=(area/'lean/AspisR1ViewParseProbe/CallerStdModels.lean').read_bytes()
start=legacy.index(b'def core.result.Result.map_err');finish=legacy.index(b'\n#print axioms Slice.Insts')
model=legacy[start:finish]
std=b'import Aeneas\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1GeometryStd\nopen Aeneas Aeneas.Std Result ControlFlow\n'+model+b'\n#print axioms core.result.Result.map_err\n#print axioms core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any\nend AspisR1GeometryStd\n'
stdpath=area/'lean/CuSavingsGeometryStd.lean'
if a.check:assert stdpath.read_bytes()==std
else:stdpath.write_bytes(std)
for n,b in files.items():
 p=area/'lean/AspisR1GeometryCandidate7'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.write_bytes(b)
meta=dict(library_model_origin='AspisR1ViewParseProbe/CallerStdModels.lean',library_model_fragment_sha256=sha(model),library_model_transport='Exact generic Result.map_err and Iterator.any model bodies, namespace-only promotion; no parser carrier imported.',raw_types_sha256=sha(raw.encode()),installed_types_sha256=sha(files['Types.lean']),raw_funs_sha256=sha(rawfuns),installed_funs_sha256=sha(files['Funs.lean']),short_string_certificates=rawfuns.count(b'toStr '),rust_computations_unchanged=True,short_string_proofs_kernel_decide=True,type_registration_transport='Replace attribute-generated unqualified global Discriminant names by explicit fully qualified instances with the exact enum-order ordinal mapping; no carrier or constructor changes.',enum_variants=[17,8])
p=t/'geometry-candidate7-emission.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=a.check,rust_computations_unchanged=True,short_string_proofs_kernel_checked=True,qualified_discriminants=True)))
