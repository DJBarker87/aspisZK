#!/usr/bin/env python3
"""Share exact original carriers; bind generic heap to exact emitted helper."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4];sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(here/'rho-accumulator-new-generated/Types.lean').read_bytes();header,*chunks=re.split(rb'(?m)(?=^/--)',raw);end=re.search(rb'\nend \w+\n$',chunks[-1]);assert end;chunks[-1]=chunks[-1][:end.start()]+b'\n'
shared=(area/'lean/AspisR1RhoPowerTail/Types.lean').read_bytes();errors=(area/'lean/AspisR1RhoInit/Types.lean').read_bytes();kept=[];names=[]
for c in chunks:
 m=re.search(rb'(?m)^(?:def|structure|inductive)\s+([\w.]+)',c);assert m;name=m[1]
 if name==b'verifier.Accumulator.new.closure':kept.append(c);continue
 clean=re.sub(rb'/--.*?-/',b'',c,flags=re.S).replace(b'@[discriminant isize]\n',b'').strip()
 if name==b'aspis_core.r0.Error':assert clean.replace(b'aspis_core.r0.Error',b'r0.Error') in errors
 elif name==b'verifier.Error':assert clean in errors
 else:assert clean in shared,name
 names.append(name.decode())
types=header.replace(b'import Aeneas\n',b'import AspisR1RhoPowerTail.Types\nimport AspisR1RhoHeap.Types\n')
types=types.replace(b'namespace AspisR1RhoAccumulatorNew\n',b'namespace AspisR1RhoPowerTail\nabbrev aspis_core.r0.Error := AspisR1CuRho.r0.Error\nabbrev verifier.Error := AspisR1CuRho.verifier.Error\nabbrev verifier.Error.Allocation := AspisR1CuRho.verifier.Error.Allocation\n')+b''.join(kept)+b'end AspisR1RhoPowerTail\n'
funs=(here/'rho-accumulator-new-generated/Funs.lean').read_bytes().replace(b'namespace AspisR1RhoAccumulatorNew\n',b'namespace AspisR1RhoPowerTail\nvariable [AspisR1CuRho.HeapReserve]\n').replace(b'end AspisR1RhoAccumulatorNew\n',b'end AspisR1RhoPowerTail\n')
external=b'''import AspisR1RhoAccumulatorNew.Types
import AspisR1RhoHeap.Funs
open Aeneas Aeneas.Std Result
namespace AspisR1RhoPowerTail
abbrev core.result.Result.map_err := @AspisR1PublicPreparation.core.result.Result.map_err
abbrev aspis_core.r0.heap.filled [AspisR1CuRho.HeapReserve] := @AspisR1CuRho.r0.heap.source_filled _
end AspisR1RhoPowerTail
'''
spec=importlib.util.spec_from_file_location('cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
heap_ref=(here/'rho-heap-input/fragments/filled.rs').read_bytes();heap_ident=[]
for revision in ['16a39d2a8a5124e25c787f2b9fcaf8449fb84611^','16a39d2a8a5124e25c787f2b9fcaf8449fb84611']:
 b=subprocess.check_output(['git','-C',str(repo),'show',revision+':crates/aspis-core/src/r0/heap.rs'])
 with tempfile.NamedTemporaryFile() as f:
  f.write(b);f.flush();item,*_=cut.find_item(Path(f.name),'pub fn filled<T: Copy>(')
 assert item==heap_ref;heap_ident.append(dict(revision=revision,filled_sha256=sha(item)))
outputs={'Types.lean':types,'Funs.lean':funs,'FunsExternal.lean':external}
for n,b in outputs.items():
 p=area/'lean/AspisR1RhoAccumulatorNew'/n
 if a.check:assert p.read_bytes()==b,n
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
meta=dict(raw_types_sha256=sha(raw),raw_funs_sha256=sha((here/'rho-accumulator-new-generated/Funs.lean').read_bytes()),shared_identical_carriers=names,heap_source_identity=heap_ident,promoted={n:sha(b) for n,b in outputs.items()},scope='Reuse identical power-tail carriers and original core/verifier errors. Namespace owner only and reserve typeclass binder added; all generated function bodies unchanged. Heap maps to exact already emitted source_filled; map_err maps to original runtime function. No template imported, allocation-success/frame/canonicality property postulated.')
p=here/'rho-accumulator-new-layout.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=a.check,generated_bodies_unchanged=True,heap_source_identical=True)))
