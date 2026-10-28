"""Static source-partition/receipt validation; no prover replay."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
def added_files(p):
 out={};name=None
 for l in p.read_text().splitlines(True):
  if l.startswith('+++ b/'):
   name=l[len('+++ b/'):].strip();out[name]=''
  elif l.startswith('+') and name:out[name]+=l[1:]
 return {n:s for n,s in out.items() if n.endswith(('/NBE_keys.rs','/NBE_multiproof.rs'))}
patches=sorted(E.glob('NBE_harness*.patch'));variants={n:set() for n in ['NBE_keys.rs','NBE_multiproof.rs']}
for p in patches:
 subprocess.run(['git','apply','--check',str(p)],cwd=R,check=True)
 for n,s in added_files(p).items():variants[Path(n).name].add(hashlib.sha256(s.encode()).hexdigest())
files=added_files(E/'NBE_harness.patch');keys=next(v for k,v in files.items() if k.endswith('/NBE_keys.rs'));mp=next(v for k,v in files.items() if k.endswith('/NBE_multiproof.rs'))
candidate=(R/'crates/aspis-r1-cost-probe/src/candidate.rs').read_text();compact=(R/'crates/aspis-r1-cost-probe/src/compact.rs').read_text()
a=candidate.index('        let u = queries[lo + j];',candidate.index('fn batch_keys'));b=candidate.index('\n    }',a);keybody=candidate[a:b];assert keybody in keys
start=candidate.index('        while j > 0',candidate.index('fn sort_batch_keys'));end=candidate.index('\n    }',start);sortbody=candidate[start:end].replace('while j > 0','if j > 0',1);assert sortbody in keys
start=compact.index('        at += 32 * SLOT_NODES[i];');end=compact.index('\n    }',start);assert compact[start:end] in keys
assoc=json.loads((E/'NBE_ROW_ASSOCIATION.json').read_text());start=mp.index('fn NBE_row<');end=mp.index('\n#[kani::proof]',start);row=mp[start:end]
# Generator's cut has one trailing newline, separated from its proof by another.
assert hashlib.sha256(row.rstrip('\n').encode()+b'\n').hexdigest()==assoc['generated_row_sha256']
checked=[]
for p in E.glob('NBE_*/receipt.json'):
 d=json.loads(p.read_text())
 for n,wanted in d['source_hashes'].items():
  if Path(n).name in variants:assert wanted in variants[Path(n).name],(p,n,wanted)
 checked.append(d['attempt'])
assert not any(x in mp+keys for x in ['kani::stub(', 'kani::stub_verified('])
for p in (R/'docs/research/100bit-spend-path-20261013/lean').glob('NBE_*.lean'):
 s=p.read_text();assert not any(x in s for x in ['sorry','native_decide','maxHeartbeats','maxRecDepth','axiom '])
(E/'NBE_STATIC_VALIDATION.json').write_text(json.dumps(dict(patches_apply=[p.name for p in patches],native_key_step_exact=True,native_sort_step_exact_except_while_to_if=True,native_slot_step_exact=True,native_row_matches_generator_hash=True,all_harness_receipt_snapshots_match_retained_patch=sorted(checked),no_function_stubs=True,new_lean_source_checks=True),indent=2)+'\n')
print('Static source/patch/receipt checks passed')
