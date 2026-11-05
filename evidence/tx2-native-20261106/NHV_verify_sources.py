"""Independent retained-source/header check; no prover or source regeneration."""
from pathlib import Path
import json,hashlib,re
B=Path.cwd();sha=lambda raw:hashlib.sha256(raw).hexdigest();x=json.loads((B/'NHV_RETARGET_ANALYSIS.json').read_text());p=json.loads((B/'NHV_RETARGET_PROVENANCE.json').read_text())
for r in p['records']:
 old=x['sources'][r['original_module']]['source'];new=(B/'NHV_generated'/(r['target']+'.lean')).read_text()
 assert sha(old.encode())==r['source_sha256'] and sha(new.encode())==r['target_sha256']
 oldbody='\n'.join(line for line in old.splitlines() if not line.startswith('import '))
 newbody='\n'.join(line for line in new.splitlines() if not line.startswith('import '))
 assert newbody=='\n'+oldbody, r['target']
cuts=json.loads((B/'NHV_SOURCE_CUTS.json').read_text());candidate=(B/'NHV_src/crates/aspis-r1-cost-probe/src/candidate.rs').read_text();suffix='\n#[cfg(kani)] #[path="NHV_native.rs"] mod NHV_native;\n';assert candidate.endswith(suffix)
assert sha(candidate[:-len(suffix)].encode())==cuts['source_file_sha256']
for m in ['NHV_WindowFrame','NHV_TailWindows','NHV_PendingPacket','NHV_InactivePacket','NHV_NativeOps','NHV_ReleaseOps']:
 s=(B/'NHV_generated'/(m+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option max(Heartbeats|RecDepth)',s,re.M),m
out=dict(status='PASS',retargeted_modules=len(p['records']),changes='imports only; non-import bodies byte-identical after the single header separator',candidate_frozen_body_sha256=cuts['source_file_sha256'],shipped_files_modified=False,authored_modules_no_admissions_or_limit_raises=True)
(B/'NHV_SOURCE_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
