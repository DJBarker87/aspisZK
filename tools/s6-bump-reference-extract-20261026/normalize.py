#!/usr/bin/env python3
"""Normalize generated source: default resources, one target-sized intrinsic."""
from pathlib import Path
import hashlib,json,tarfile
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021/s6-bump-reference-extraction-v1'
S=B/'lean-candidates/s126-caller-boundary-20261021/S6BumpOwnedReferenceSourceV1.lean'
E.mkdir(exist_ok=True)
with tarfile.open('/tmp/s126-bump-reference-source-export-20261026.tar.gz')as archive:
 for member in archive.getmembers():
  assert member.isfile()and not Path(member.name).is_absolute()and'..'not in Path(member.name).parts
  assert Path(member.name).suffix in ['.json','.log','.rs','.toml','.lock','.txt','.py','.v1','.v2']
  target=E/member.name;target.parent.mkdir(parents=True,exist_ok=True)
  value=archive.extractfile(member).read()
  assert not target.exists()or target.read_bytes()==value
  target.write_bytes(value)
raw=(E/'source-export/raw-Funs.lean.txt').read_text()
info=json.loads((E/'source-export/target-info.json').read_text())
assert info[0]['value']['target_pointer_size']==8
assert info[0]['key']=='x86_64-unknown-linux-gnu'
rewrites={
 'import Aeneas\n':'import S6StdOptionSourceV1\n', # Reuse checked Option discriminants.
 'import AspisS6BumpOwnedReference.Types\n':'', # Independently checked empty.
 'import AspisS6BumpOwnedReference.FunsExternal\n':'',
 'set_option maxHeartbeats 1000000\n':'', # Restore default, never raise limits.
 'set_option maxRecDepth 2048\n':'',
 'let i1 ← core.mem.size_of Std.Usize':'let i1 ← ok (8#usize)',
}
result=raw
for before,after in rewrites.items():
 assert result.count(before)==1,(before,result.count(before))
 result=result.replace(before,after)
assert 'core.mem.size_of'not in result
assert 'axiom 'not in result and 'sorry'not in result
audits=['AspisS6BumpOwnedReference.step',
 'AspisS6BumpOwnedReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch',
 'AspisS6BumpOwnedReference.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual']
result+='\n'+'\n'.join('#print axioms '+name for name in audits)+'\n'
S.write_text(result)
sha=lambda b:hashlib.sha256(b).hexdigest()
(E/'normalization.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1',
 'raw_source_sha256':sha(raw.encode()),'normalized_source_sha256':sha(result.encode()),
 'rewrites':rewrites,'appended_axioms_reports':audits,'sizeof_specialization':{'type':'Std.Usize','bytes':8,'target_information':'source-export/target-info.json'},
 'qualification':'Only the monomorphic size_of::<usize>() call is resolved from target metadata. Option Try/FromResidual are actual emitted bodies. No generic size_of interpretation, custom axiom, opaque helper or resource override is installed. This is source extraction/normalization, not SDK/native or SBF closure.'},indent=2)+'\n')
print(str(S))
