#!/usr/bin/env python3
"""Collect binder-sensitive owner audit; no theorem/raw-data/source replacement."""
from pathlib import Path
import json,hashlib,shutil,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-literal-comparison-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
attempts=['sdk-literal-comparator-v2','sdk-literal-data-audit-v1'];ledger={}
for attempt in attempts:
 d=E/attempt;r=json.loads((d/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0 and '-j1' in r['command'] and '-M4400' in r['command']
 ledger[attempt]={k:r[k] for k in ['target','source_sha256','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']}
lines=(E/'sdk-literal-data-audit-v1/lean.log').read_text().splitlines();groups={}
for label in ['CURRENT_DUP','FACTOR','FACTOR_INPUT_DUP','REFRESH']:
 groups[label]=[json.loads(l[len(label)+1:]) for l in lines if l.startswith(label+' ')]
summary=json.loads(next(l[len('LITERAL_SUMMARY '):] for l in lines if l.startswith('LITERAL_SUMMARY ')))
assert summary==dict(current_alpha_duplicates=43,current_constants=28518,current_duplicates=43,current_literal_duplicates=43,factor_alpha=233,factor_input_duplicates=0,factor_input_literal_duplicates=0,factor_literal=182,factor_missing=3,factor_paired=236,factor_type_alpha=236,factor_type_literal=212,refresh_count=6,refresh_type_alpha=6,refresh_type_literal=6)
assert all(r['comparison']['literal'] for r in groups['CURRENT_DUP']) and all(r['comparison']['type_literal'] and r['comparison']['both_theorems'] for r in groups['REFRESH'])
config=json.loads((P/'input.json').read_text());pins=json.loads((P/'input-pins.json').read_text());post=[]
for row in pins['inputs']+pins['transport_files']:
 p=Path(row['path']);post.append(dict(path=str(p),unchanged=p.is_file() and p.stat().st_size==row['bytes'] and sha(p)==row['sha256']))
assert all(r['unchanged'] for r in post)
(P/'post-inputs.json').write_text(json.dumps(dict(all_unchanged=True,files=post),separators=(',',':'))+'\n')
(P/'results.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',summary=summary,groups=groups,factor_nonliteral_names=[r['name'] for r in groups['FACTOR'] if not r['comparison']['literal']],factor_nonliteral_type_names=[r['name'] for r in groups['FACTOR'] if not r['comparison']['type_literal']],selection=dict(current_duplicate_coalescing_literal_guard=True,proof_refresh_type_literal_guard=True,whole_factor_literal_identity=False,original_ROOT_current_join=False,kernel_reconstruction=False),scope='Owner CURRENT data literal duplicate guard and exact proof-refresh types; full original/factored identity is FALSE at this scope, with all 54 differences/24 type differences preserved. No source/native/security closure.'),indent=2)+'\n')
(P/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
W=Path('/private/tmp/s126-sdk-literal-comparison-release-20261025-v1');W.mkdir(mode=0o700,exist_ok=False)
for p in P.iterdir():
 if p.is_file():shutil.copyfile(p,W/p.name)
for attempt in ['sdk-literal-comparator-v1',*attempts]:
 d=W/attempt;d.mkdir()
 for name in ['source.lean','command.json','receipt.json','lean.log','time.log']:shutil.copyfile(E/attempt/name,d/name)
(W/'README.txt').write_text('BINDER-SENSITIVE CURRENT SDK DATA AUDIT / HISTORICAL QUALIFICATION\nNo raw constant payloads or theorem source are replaced. Reuse the THREE immutable raw-data releases named in input-pins.json.\n43/43 CURRENT duplicate declaration comparisons pass full metadata plus Expr.equal type/value/opaque/recursor RHS guards. 6/6 refreshed public proof types pass Expr.equal.\nOriginal/factored scope:182/236 declarations literal,233/236 legacy alpha+metadata,212/236 types literal,236/236 types alpha,3new auxiliaries.54nonliteral declarations are NOT silently selected as literal matches.\nHistorical Port18 sameDeclaration guards used BEq Expr=Expr.eqv, ignoring binder names/annotations. All old strict/identical/type-equality descriptions based solely on that helper are QUALIFIED; old receipts/raw terms unchanged. New literal results are separate evidence, not retrospective proof.\nSynthetic comparison fixtures are data only, never trusted declarations. No kernel reconstruction, original ROOT/current join, native source/ABI, artifact or security closure.\n')
files=[dict(relative=str(p.relative_to(W)),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(W.rglob('*')) if p.is_file()]
m=dict(schema='focused-extractor-proof-packet-v1',kind='binder-sensitive-data-audit-companion-not-raw-replacement',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),bases=pins['bases'],summary=summary,ledger=ledger,files=files,scope='Current literal duplicate/type guards with explicit false full-factor literal identity; no kernel, native, release or security closure.')
(W/'manifest.json').write_text(json.dumps(m,indent=2)+'\n');mb=(W/'manifest.json').read_bytes()
for p in W.rglob('*'):
 if p.is_file():p.chmod(0o444)
for p in sorted([p for p in W.rglob('*') if p.is_dir()],key=lambda p:len(p.parts),reverse=True):p.chmod(0o555)
W.chmod(0o555)
(P/'release-manifest.json').write_bytes(mb);(P/'release.json').write_text(json.dumps(dict(location=str(W),manifest_sha256=hashlib.sha256(mb).hexdigest(),scope=m['scope']),indent=2)+'\n')
print(json.dumps(dict(location=str(W),summary=summary)))
