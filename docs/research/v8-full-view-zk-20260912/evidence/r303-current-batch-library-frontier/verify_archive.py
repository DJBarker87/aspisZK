#!/usr/bin/env python3
"""Verify copied archive files against original scratch artifacts and SHA256SUMS."""
import hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[2]
ARCH=pathlib.Path(__file__).resolve().parent
SRC=ROOT/'.r21-scratch'
NAMES=['r280-private-norm-batch-extract','r282-private-norm-closures-extract','r283-private-norm-batch-extract','r288-private-batch-ordering','r290-private-batch-ordering','r292-original-r283-order-audit','r292-private-batch-translation','r293-private-norm-batch-extract','r294-private-norm-batch-extract','r295-private-batch-translation','r295-signature-failure-inventory','r296-monomorphization-preflight','r297-private-norm-batch-monomorphized','r303-private-batch-translation']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
for name in NAMES:
 src=SRC/name; dst=ARCH/'artifacts'/name
 src_files={p.relative_to(src).as_posix() for p in src.rglob('*') if p.is_file()}
 expected=src_files-({'decoded.json'} if name=='r280-private-norm-batch-extract' else set())
 if name in ('r292-original-r283-order-audit','r292-private-batch-translation'): expected.add('inputs/R283PrivateNormBatch.llbc')
 dst_files={p.relative_to(dst).as_posix() for p in dst.rglob('*') if p.is_file()}
 assert expected==dst_files,(name,sorted(expected-dst_files),sorted(dst_files-expected))
 for rel in sorted(expected):
  if rel in src_files:
   assert sha(src/rel)==sha(dst/rel),(name,rel)
 checks.append({'directory':name,'files_equal':len(expected),'preserved_byte_identically':True,'only_allowed_omission': 'decoded.json' if name=='r280-private-norm-batch-extract' else None})
for name in ['r292-original-r283-order-audit','r292-private-batch-translation']:
 p=ARCH/'artifacts'/name/'inputs/R283PrivateNormBatch.llbc'
 src=SRC/'r283-private-norm-batch-extract/R283PrivateNormBatch.llbc'
assert sha(p)==sha(src)
for name in ['r303-private-batch-translation']:
 p=ARCH/'artifacts'/name/'R297PrivateNormBatch.input.llbc'
 src=SRC/'r297-private-norm-batch-monomorphized/R297PrivateNormBatch.llbc'
 assert sha(p)==sha(src)
manifest=json.loads((ARCH/'manifest.json').read_text())
omit=SRC/'r280-private-norm-batch-extract/decoded.json'
assert omit.stat().st_size==manifest['omissions'][0]['size_bytes']
assert sha(omit)==manifest['omissions'][0]['sha256']
sums=[]
for line in (ARCH/'SHA256SUMS').read_text().splitlines():
 want,rel=line.split('  ',1);p=ARCH/rel;got=sha(p) if p.is_file() else None
 sums.append((rel,want==got))
assert sums and all(ok for _,ok in sums)
history=ARCH/'prior-prepared-r295-candidate-history'
for n in ['README.md','manifest.json','SHA256SUMS','verification.json']:
 assert (history/n).is_file()
report={'all_passed':True,'source_directory_checks':checks,'extra_R283_input_snapshots':2,'extra_R297_input_snapshots':1,'prior_R295_candidate_history_files':['prior-prepared-r295-candidate-history/README.md','prior-prepared-r295-candidate-history/manifest.json','prior-prepared-r295-candidate-history/SHA256SUMS','prior-prepared-r295-candidate-history/verification.json'],'R280_decoded_omitted_size_bytes':omit.stat().st_size,'R280_decoded_sha256':sha(omit),'archive_checksum_entries_checked':len(sums),'archive_checksum_mismatches':[]}
(ARCH/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
