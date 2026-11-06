"""Supplement original scope receipts without altering any captured receipt bytes."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
features=json.loads((E/'PCE_DEPLOYED_FEATURES.json').read_text());ats=[json.loads(l) for l in (E/'PCE_ATTEMPTS.jsonl').read_text().splitlines()];pins=json.loads(lzma.decompress((E/'PCE_IMPORTS.json.xz').read_bytes()));contexts=[]
for rc in ats:
 a=rc['attempt'];p=E/a/'receipt.json';ad=json.loads((E/(a+'-admission.json')).read_text());disks=[json.loads(p.read_text()) for p in E.glob(a+'-disk-*.json')];assert ad['exit']==0 and ad['reservation']['allowed'] is True and disks[-1]['free']>=40_000_000_000
 x=dict(attempt=a,target=rc['module'],exit_status=rc['exit_status'],wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'],source_revision=rc['source_revision'],source_hashes=rc['source_hashes'],print_axioms=rc['print_axioms'],receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),receipt=str(p.relative_to(E)),admission=ad,disk_before=disks[-1],deployed_feature_resolution=features,feature_scope='Inherited all-crate selected features; PCE compiles/audits Lean only, no Rust body changed',Aeneas_pin_manifest='PCE_IMPORTS.json.xz',pinned_Aeneas_files=sum(v['module'].startswith(('Aeneas.','AeneasMeta.')) or v['module'] in ['Aeneas','AeneasMeta'] for v in pins.values()),source_assessment='No shipped source, protocol, feature, artifact or trust-boundary change; default/devnet/Pool ELF pins inherited, not rebuilt')
 (E/a/'PCE_CONTEXT.json').write_text(json.dumps(x,indent=1)+'\n');contexts.append(dict(attempt=a,context=a+'/PCE_CONTEXT.json',receipt=x['receipt'],exit_status=rc['exit_status']))
(E/'PCE_SCOPE_CONTEXTS.json').write_text(json.dumps(contexts,indent=1)+'\n');print('Supplemented'+str(len(contexts))+' original receipts with exact metrics, source/axiom fields and inherited all-crate feature tables.')
