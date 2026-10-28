"""Bind native GenericArray representation declarations to the reference carriers."""
from pathlib import Path
import subprocess,json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
code='''from pathlib import Path
import json,hashlib,tarfile
p=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/generic-array-0.14.7/src/lib.rs');a=Path('/home/dombarker/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/generic-array-0.14.7.crate')
assert hashlib.sha256(a.read_bytes()).hexdigest()=='85649ca51fd72272d7821adaf274ad91c288277713d9c18820d8499a7ff69e9a'
with tarfile.open(a) as archive:assert p.read_bytes()==archive.extractfile('generic-array-0.14.7/src/lib.rs').read()
print(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source=p.read_text())))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);s=j.pop('source');declarations={}
for name,representation,expected in [('GenericArrayImplEven','C','parent1:U,parent2:U,_marker:PhantomData<T>,'),('GenericArrayImplOdd','C','parent1:U,parent2:U,data:T,'),('GenericArray','transparent','data:U::ArrayType,')]:
 match=re.search(r'#\[repr\('+representation+r'\)\](?:\s*#\[[^\n]*\])*\s*pub struct '+name+r'<[^\n]+>\s*\{([^}]+)\}',s)
 assert match,name
 assert ''.join(match.group(1).split())==expected,(name,match.group(1))
 declarations[name]=match.group(0)
out=dict(source=j,declarations=declarations,whole_field_bodies_and_repr_checked=True,archive_checksum_checked=True,reference='PV_CBL_LibraryShapes.Even/Odd/GenericArray, PV_CBL_GenericArrayPower.Storage and PV_DL_ArrayShape.Carrier',differences=[dict(native='PhantomData marker and native zero-length array',reference='Unit marker and length-zero Array subtype',proof='StorageIdentity.zero_array/injective/rebuild; unique Unit fields; ArrayShape.length/reconstruct'),dict(native='repr(C) contiguous u8 field hierarchy under repr(transparent) outer array',reference='left subtree then right subtree then odd byte',proof='GenericArrayPower.length, StorageBuild.flatten_build/reconstruct, ArrayShape.flatten_build/reconstruct; UpdateViews.native_bulk/byte/native_block_lengths')],scope='Original u8 layouts, powers32/64 and native odd/even28. Native/compiler representation rules remain in E1/E2; no new trust field or backend equality introduced.',finite_validation='wrappers-native-combined-resume4/receipt.json; full native buffers and output arrays checked finitely')
(E/'native-array-layout-binding.json').write_text(json.dumps(out,indent=2)+'\n');print('three complete native field bodies and repr annotations checked against pinned crate archive')
