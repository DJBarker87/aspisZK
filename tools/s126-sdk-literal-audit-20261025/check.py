#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,sys,stat
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';P=E/'sdk-literal-comparison-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((P/'release.json').read_text());m=json.loads((P/'release-manifest.json').read_text());assert sha(P/'release-manifest.json')==r['manifest_sha256']
x=json.loads((P/'results.json').read_text());assert x['summary']==m['summary'] and x['selection']['current_duplicate_coalescing_literal_guard'] and x['selection']['proof_refresh_type_literal_guard'] and not x['selection']['whole_factor_literal_identity'] and not x['selection']['kernel_reconstruction']
assert len(x['groups']['CURRENT_DUP'])==43 and all(r['comparison']['literal'] for r in x['groups']['CURRENT_DUP'])
assert len(x['groups']['REFRESH'])==6 and all(r['comparison']['type_literal'] for r in x['groups']['REFRESH'])
assert len(x['factor_nonliteral_names'])==54 and len(x['factor_nonliteral_type_names'])==24
for attempt,row in m['ledger'].items():
 d=E/attempt;rec=json.loads((d/'receipt.json').read_text());assert all(rec[k]==v for k,v in row.items()) and rec['exit_status']==0 and rec['swaps']==0 and sha(d/'source.lean')==rec['source_sha256']==sha(S/(rec['target']+'.lean'))
 assert '-j1' in rec['command'] and '-M4400' in rec['command']
assert 'LITERAL_COMPARATOR_TEST PASS' in (E/'sdk-literal-comparator-v2/lean.log').read_text()
assert json.loads((E/'sdk-literal-comparator-v1/receipt.json').read_text())['exit_status']!=0
post=json.loads((P/'post-inputs.json').read_text());assert post['all_unchanged'] and all(r['unchanged'] for r in post['files'])
for name,row in json.loads((P/'api-pins.json').read_text()).items():assert sha(P/('Lean-'+name))==row['sha256']
expr=(P/'Lean-Expr.lean').read_text();assert 'beq := Expr.eqv' in expr and 'opaque equal (a : @& Expr)' in expr
helper=json.loads((P/'helper-source.json').read_text());old=(S/'S126SdkTransportAuditV1.lean').read_text();assert hashlib.sha256(old.encode()).hexdigest()==helper['source_sha256'];a=old.index('def sameDeclaration');z=old.index('def readComplete');assert old[a:z].replace('def sameDeclaration','def sameDeclarationAlphaMetadata',1) in (S/'S126SdkLiteralComparisonV1.lean').read_text()
for rel,h in json.loads((P/'tool-pins.json').read_text()).items():assert sha(R/rel)==h
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.o','.a','.pyc'] for p in P.rglob('*') if p.is_file())
if '--released' in sys.argv:
 d=Path(r['location']);assert sha(d/'manifest.json')==r['manifest_sha256'] and stat.S_IMODE(d.stat().st_mode)&0o222==0
 for f in m['files']:
  p=d/f['relative'];assert p.is_file() and not p.is_symlink() and sha(p)==f['sha256'] and p.stat().st_size==f['bytes'] and stat.S_IMODE(p.stat().st_mode)&0o222==0
print(json.dumps(dict(status='PASS',current_literal_duplicates=43,refresh_literal_types=6,factor_literal_declarations=182,factor_paired=236,factor_literal_types=212,whole_factor_literal_identity=False,original_ROOT_current_or_kernel_join=False,released_hashed='--released' in sys.argv,scope=m['scope'])))
