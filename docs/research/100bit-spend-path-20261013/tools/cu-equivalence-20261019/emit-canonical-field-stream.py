#!/usr/bin/env python3
"""Share byte-identical emitted raw carriers; retain exact consumer bodies."""
from pathlib import Path
import argparse,re,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
def blocks(raw):
 header,*chunks=re.split(rb'(?m)(?=^/--)',raw);assert chunks[-1].endswith(b'end AspisR1CanonicalDots\n');chunks[-1]=chunks[-1][:-len(b'end AspisR1CanonicalDots\n')];out={}
 for chunk in chunks:
  m=re.search(rb'(?m)^(?:def\s+|def\s*\n\s*|structure\s+|inductive\s+)([\w.]+)',chunk);assert m,chunk[:150];name=m[1].decode();assert name not in out;out[name]=chunk
 return header,out
strip=lambda b:re.sub(rb'/--.*?-/',b'',b,flags=re.S).strip()
raw=(tool/'canonical-field-stream-generated/Types.lean').read_bytes();header,new=blocks(raw);_,old=blocks((tool/'canonical-dots-generated/Types.lean').read_bytes());shared=[]
for name in list(new):
 if name in old:assert strip(new[name])==strip(old[name]),name;shared.append(name);del new[name]
header=header.replace(b'import Aeneas\n',b'import AspisR1CanonicalDots.Funs\n')
reader=(tool/'canonical-reader-generated/Types.lean').read_bytes()
_,readerblocks=blocks(reader.replace(b'end AspisR1CanonicalReader\n',b'end AspisR1CanonicalDots\n'))
assert strip(new['verifier.Error']).replace(b'verifier.Error',b'Error')==strip(readerblocks['Error'])
errornames=['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation']
new['verifier.Error']=b'abbrev verifier.Error := AspisR1CanonicalReader.Error\n'+b''.join(('abbrev verifier.Error.'+n+' := AspisR1CanonicalReader.Error.'+n+'\n').encode() for n in errornames)+b'\n'
header=header.replace(b'import AspisR1CanonicalDots.Funs\n',b'import AspisR1CanonicalDots.Funs\nimport AspisR1CanonicalReader.Types\n')
types=header+b''.join(new.values())+b'end AspisR1CanonicalDots\n'
funsraw=(tool/'canonical-field-stream-generated/Funs.lean').read_bytes();marker=b'namespace AspisR1CanonicalDots\n';assert funsraw.count(marker)==1;funs=funsraw.replace(marker,marker+b'variable [Shared]\n',1);assert funs.replace(b'variable [Shared]\n',b'',1)==funsraw
external=(area/'lean/AspisR1CanonicalFieldStream/FunsExternal.lean').read_bytes()
mapper_source=(area/'lean/bridge-public-callers-c16-20261016/AspisR1PublicPreparation/Funs.lean').read_bytes()
mapper=mapper_source[mapper_source.index(b'def core.result.Result.map_err'):];mapper=mapper[:mapper.index(b'/--')].strip()
assert mapper in (area/'lean/CanonicalVectorExternal.lean').read_bytes()
assert b'import CanonicalVectorExternal\n' in external
assert b'def core.result.Result.map_err' not in external
assert b'import ExtractedFirstCallerReachability' not in external
assert b'let value \xe2\x86\x90 AspisR1CanonicalInputs.weights.field bytes index' in external
assert b'.ok (AspisR1.CuSavingsCanonicalDotsSources.inputToDot value)' in external
meta=dict(mapper_exact_source_sha256=sha(mapper),mapper_shared_from='CanonicalVectorExternal',external_sha256=sha(external),error_carrier='Exact emitted enum declaration alias to AspisR1CanonicalReader.Error',shared_nominal_declarations=shared,raw_types_sha256=sha(raw),raw_funs_sha256=sha(funsraw),installed_types_sha256=sha(types),installed_funs_sha256=sha(funs),scope='Shared source carriers have byte-identical emitted declaration bodies after doc removal. All new consumer declarations/bodies retained; only exact old/new API source definitions imported and a Shared instance binder inserted.')
outputs={'Types.lean':types,'Funs.lean':funs}
for name,data in outputs.items():
 p=area/'lean/AspisR1CanonicalFieldStream'/name
 if args.check:assert p.read_bytes()==data,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
p=tool/'canonical-field-stream-emission.json';data=(json.dumps(meta,indent=2)+'\n').encode()
if args.check:assert p.read_bytes()==data
else:p.write_bytes(data)
print(json.dumps(dict(check=args.check,shared=len(shared),consumer_bodies_unchanged=True)))
