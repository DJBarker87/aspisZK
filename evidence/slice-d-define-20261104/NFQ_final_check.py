"""Final metadata/admission checks only. This never launches a prover."""
from pathlib import Path
import subprocess,json,hashlib,time,re,lzma,ast
E=Path(__file__).resolve().parent;R=E.parents[1];start=time.monotonic();checks=[]
for script in ['NFQ_validate.py','NFQ_certify.py']:
 r=subprocess.run(['python3',str(E/script)],capture_output=True,text=True,cwd=R)
 checks.append(dict(target=script,exit_status=r.returncode,stdout=r.stdout,stderr=r.stderr))
 assert r.returncode==0,(script,r.stdout,r.stderr)
required=['NFQ_SLICE_D.json','NFQ_SLICE_D.md','NFQ_COVERAGE.md','NFQ_ORDER.md','NFQ_BRIDGES.md','NFQ_CLOSED.json','NFQ_LEDGER_DELTA.json','NFQ_AUDIT.json','NFQ_HANDOFF.md','NFQ_REMAINING.md','NFQ_ATTEMPTS.jsonl']
assert all((E/n).is_file() for n in required)
for p in E.rglob('*.py'):ast.parse(p.read_text(),filename=str(p))
assert not list(E.rglob('__pycache__'))
assert all(p.stat().st_size<20_000_000 for p in E.rglob('*') if p.is_file())
# Every new .lean theorem entering final audit has its current source compiled,
# and the whole new group coexists with the canonical deployed theorem.
imports=(E/'NFQ_STAGE2_IMPORT.lean').read_text();roots=json.loads((E/'NFQ_STAGE2_ROOTS.json').read_text());audit=json.loads((E/'NFQ_AUDIT.json').read_text())
assert len(roots)==36 and set(roots)<=audit['raw_roots'].keys()
assert len(audit['raw_roots'])==42
for line in imports.splitlines():
 if line.startswith('import '):
  module=line[7:];source=(E/(module+'.lean')).read_bytes();digest=hashlib.sha256(source).hexdigest()
  receipts=[json.loads(p.read_text()) for p in E.glob('NFQ_L???/receipt.json')]
  assert any(r['module']==module and r['exit_status']==0 and digest in r['source_hashes'].values() for r in receipts),module
l48=json.loads((E/'NFQ_L048/receipt.json').read_text());assert any("'AspisR1.RPx_Deployed.deployed'" in x for x in l48['print_axioms'])
for name in ['NFQ_CACHE_IMPORTS.json','NFQ_COMPOSED_LEDGER.json']:
 raw=lzma.decompress((E/(name+'.xz')).read_bytes());expected=(E/(name+'.sha256')).read_text().split()[0];assert hashlib.sha256(raw).hexdigest()==expected
attempts=json.loads((E/'NFQ_ATTEMPTS_INDEX.json').read_text());assert len(attempts['attempts'])==113 and attempts['budget']['Kani']['charged']==60 and attempts['budget']['Lean_support']['charged']==50 and attempts['budget']['extraction']['charged']==3
changed=subprocess.check_output(['git','diff','--name-only','121ea8f9b22'],cwd=R,text=True).splitlines();assert all(x.startswith(str(E.relative_to(R))+'/') for x in changed)
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
source_names=['NFQ_validate.py','NFQ_certify.py','NFQ_final_check.py','NFQ_SLICE_D.json','NFQ_COVERAGE.json','NFQ_ORDER.json','NFQ_CLOSED.json','NFQ_CERTIFICATES.json','NFQ_EDGES.json','NFQ_AUDIT.json','NFQ_HANDOFF.md','NFQ_REMAINING.md','NFQ_FEATURE_PARITY.json','NFQ_FINDINGS.md','NFQ_DOMAIN_FINDINGS.json']
result=dict(exit_status=0,source_revision=head,source_tree_dirty=True,wall_seconds=time.monotonic()-start,checks=checks,new_composed_functions=16,new_composed_rows=21,remaining_D_rows=322,coverage='585/587',prover_runs_in_this_validation=0,raw_audit='NFQ_L050 plus reused NFQ_L010',source_sha256={n:hashlib.sha256((E/n).read_bytes()).hexdigest() for n in source_names},shipped_changes=False,ELF_rebuild_trigger=False,all_required_outputs=True,max_file_bytes=max(p.stat().st_size for p in E.rglob('*') if p.is_file()),pycache_present=False)
(E/'NFQ_FINAL.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps({k:result[k] for k in ['exit_status','new_composed_functions','new_composed_rows','remaining_D_rows','coverage','prover_runs_in_this_validation']}))
