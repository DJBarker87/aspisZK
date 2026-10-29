"""Package only public receipts; key directories are never traversed."""
import gzip,hashlib,json,pathlib,tarfile
ROOT=pathlib.Path('/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029');E=ROOT/'evidence/devnet-rehearse-20261029'
files=[]
for directory in ('NDZ_final_deploy','NDZ_final_spend','NDZ_final_failure'):
 for p in (E/directory).rglob('*'):
  if p.is_file():
   assert 'keys' not in p.relative_to(E).parts and 'client64-proof-private' not in str(p)
   files.append(p)
manifest={str(p.relative_to(E)):{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(files)}
with gzip.open(E/'NDZ_RECEIPT_MANIFEST.json.gz','wt') as f:json.dump(manifest,f,sort_keys=True)
roots=['NDZ_SUMMARY.json','NDZ_TRANSACTIONS.json','NDZ_RENT_LEDGER.json','NDZ_LOCAL_KEYS_PUBLIC.json','NDZ_PROOF_REUSE.json','NDZ_FINAL_BUFFERS.json','NDZ_COLLECTION_AUDIT.json','NDZ_METADATA.json.gz','NDZ_RECEIPT_MANIFEST.json.gz','NDZ_local.json','NDZ_VALIDATOR_RESOURCE.json','NDZ_final_deploy-receipt.json','NDZ_final_deploy.time','NDZ_final_deploy.log','NDZ_final_spend-receipt.json','NDZ_final_spend.time','NDZ_final_spend.log','NDZ_final_failure-receipt.json','NDZ_final_failure.time','NDZ_final_failure.log','NDZ_final_failure.json','NDZ_reservations_before_spend.json','NDZ_spend-receipt.json','NDZ_spend.time','NDZ_final-validator.time']
for name in ['NDZ_ASSOCIATION.json','NDZ_final-immutable.json','NDZ_local-preflight.json']:
 with gzip.open(E/(name+'.gz'),'wb') as f:f.write((E/name).read_bytes())
 roots.append(name+'.gz')
for name in ['NDZ_client-build4.time','NDZ_client-build4.log','NDZ_runtime.log']:
 p=ROOT/name
 if p.exists():
  (E/name).write_bytes(p.read_bytes());roots.append(name)
with tarfile.open(E/'NDZ_PUBLIC_RECEIPTS.tar.gz','w:gz') as tar:
 for name in roots:tar.add(E/name,arcname=name)
 for p in files:
  rel=p.relative_to(E)
  if rel.parts[0]=='NDZ_final_deploy' and (p.name.startswith(('tx-','verifier-write-')) or p.name=='verifier-signatures.json'):continue
  tar.add(p,arcname=str(rel))
print({'raw_public_receipt_files':len(files),'archive_bytes':(E/'NDZ_PUBLIC_RECEIPTS.tar.gz').stat().st_size})
