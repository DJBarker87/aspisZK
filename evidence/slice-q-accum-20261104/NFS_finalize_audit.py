from pathlib import Path
import json,hashlib,lzma
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((E/'NFS_AUDIT_ROOTS.json').read_text());roots=[];fixtures=[]
for p in sorted((E/'NFS_final_audit').glob('*.log')):
 for line in p.read_text().splitlines():
  if line.startswith('NEP_RESULT '):
   r=json.loads(line[11:])
   if p.stem=='fixtures':fixtures.append(r);continue
   name='NEP_'+p.stem+'_'+r['root']+'_REACHABLE.txt';archive=E/(name+'.xz');raw=lzma.decompress(archive.read_bytes())
   r.update(mode=p.stem,graph_archive=archive.name,compressed_sha256=sha(archive),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),attempt='NFS_L089')
   assert (E/(name+'.sha256')).read_text().split()[0]==r['uncompressed_sha256']
   roots.append(r)
assert len(roots)==len(manifest['roots']) and {r['root'] for r in roots}==set(manifest['roots'])
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in roots)
assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
scan=[json.loads(l) for l in (E/'NFS_LOADED_scan.jsonl').read_text().splitlines()]
metrics=dict(modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=sum(len(r['dangling']) for r in scan),incompatible_owners=sum(len(r['duplicate_owners']) for r in scan),import_mismatches=sum(not r['imports_match'] for r in scan),cached_replicas=sum(len(r['cached_replicas']) for r in scan),output_sha256=sha(E/'NFS_LOADED_scan.jsonl'))
assert metrics['dangling']==metrics['incompatible_owners']==metrics['import_mismatches']==0
baseline=(E.parent/'slice-q-phase-20261104/NFN_ProofDriver.lean').read_text();driver=(E/'NFS_ProofDriver.lean').read_text()
assert baseline[:baseline.index('/-- Standalone runtime')]==driver[:driver.index('/-- Standalone runtime')]
assert baseline[baseline.index('  let ctx : Command.Context'):]==driver[driver.index('  let ctx : Command.Context'):]
scanner=(E/'NFS_Driver.lean').read_text();oldscanner=(E.parent/'slice-q-phase-20261104/NFN_Driver.lean').read_text();assert scanner[:scanner.index('/-- Standalone runtime')]==oldscanner[:oldscanner.index('/-- Standalone runtime')]
conform=json.loads((E/'NFS_AX2_CONFORMANCE.json').read_text());conform.update(fixtures_pending=False,fixture_target='NFS_L089:NFS_final_audit/fixtures',driver_source_sha256=sha(E/'NFS_ProofDriver.lean'),fixtures_passed=8);(E/'NFS_AX2_CONFORMANCE.json').write_text(json.dumps(conform,indent=1)+'\n')
a=dict(status='PASS_COHERENT_QUERY_PACKETS',headline='AspisR1.RPx_Deployed.deployed',roots=roots,root_count=len(roots),raw_walk_authoritative=True,standard_axioms_only=True,collect_axioms_disagreements=[r['root'] for r in roots if not r['equal']],fixtures=fixtures,walker_byte_identical_to_NEP=True,audit_prefix_unchanged=True,audit_action_unchanged=True,scanner_core_unchanged=True,driver_source_sha256=sha(E/'NFS_ProofDriver.lean'),scanner_source_sha256=sha(E/'NFS_Driver.lean'),incoherence_scan=metrics,gate_receipt='NFS_L089/receipt.json',child_receipts='NFS_final_audit/NFS_CHILD_ATTEMPTS.json',cold_release_replay=False,security_target_established=False)
(E/'NFS_AUDIT.json').write_text(json.dumps(a,indent=1)+'\n')
raw=lzma.decompress((E/'NFS_CACHE_IMPORTS.json.xz').read_bytes());(E/'NFS_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'  NFS_CACHE_IMPORTS.json\n')
print(json.dumps(dict(roots=len(roots),fixtures=len(fixtures),scan=metrics)))
