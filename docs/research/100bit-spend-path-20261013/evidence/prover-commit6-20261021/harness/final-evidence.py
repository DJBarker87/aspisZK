#!/usr/bin/env python3
import hashlib,json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
old=E.parent/'prover-commit5-20261021'
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
inv=json.loads((old/'elf-source-inventory.json').read_text())
diffs=[]
for rel,h in inv['files'].items():
 if not Path(rel).exists() or hashlib.sha256(Path(rel).read_bytes()).hexdigest()!=h:diffs.append(rel)
assert not diffs,diffs
frozen=json.loads((old/'frozen-elf-final-check.json').read_text())
meta=dict(current_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 inherited_source_revision=inv['source_revision'],matched_source_files=len(inv['files']),all_source_hashes_match=True,
 inherited_cmp_evidence=pin(old/'frozen-elf-final-check.json'),inherited_build_receipts=[pin(old/'build'/('build-'+n+'-final')/'receipt.json') for n in ['default','devnet','pool']],
 programs={k:{n:v[n] for n in ['sha256','size_bytes','cmp_exit','byte_identical']} for k,v in frozen['programs'].items()},
 fresh_rebuild=False,reason='No tracked release input changed; AGENTS forbids unchanged full regression.',
 binaries_committed=False,keys_created_read_deleted=False)
(E/'elf-inheritance.json').write_text(json.dumps(meta,indent=2)+'\n')
# Exact release source and matching accepted receipts.
manifest=json.loads((E/'new-cone-manifest.json').read_text())
receipts=[json.loads(p.read_text()) for p in sorted((E/'lean').glob('lean-*.json'))]
source=[]
for m in manifest['modules']:
 p=Path('docs/research/v8-r0-zk-20261009/lean')/('R1Z/'+m+'.lean')
 x=pin(p);r=next((r for r in reversed(receipts) if r['source_sha256']==x['sha256'] and int(re.search(r'^exit=(\d+)',(E/'lean'/f"out-{r['attempt']}.log").read_text(),re.M)[1])==0),None)
 assert r,m
 x.update(accepted_attempt=r['attempt'],source_revision=meta['current_revision']);source.append(x)
(E/'source-release.json').write_text(json.dumps(source,indent=2)+'\n')
print(json.dumps(dict(elf_inputs_verified=len(inv['files']),release_modules=len(source))))
