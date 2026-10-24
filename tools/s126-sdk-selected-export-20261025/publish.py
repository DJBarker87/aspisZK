#!/usr/bin/env python3
"""Publish only the new selected-cut raw terms; no kernel trust operation."""
from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-selected-cut-export-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
config=json.loads((P/'input.json').read_text());pins=json.loads((P/'input-pins.json').read_text());W=Path(config['dest']).parent;dest=Path('/private/tmp/s126-sdk-selected-cut-release-20261025-v1');assert not dest.exists()
def one(lines,prefix):
 xs=[json.loads(l[len(prefix):]) for l in lines if l.startswith(prefix)];assert len(xs)==1;return xs[0]
export=E/'sdk-selected-cut-export-v1';audit=E/'sdk-selected-cut-audit-v2';ex=(export/'lean.log').read_text().splitlines();au=(audit/'lean.log').read_text().splitlines();a=one(au,'AUDIT_SUMMARY ');s=one(ex,'SUMMARY ')
assert a['baseline_constants']==s['baseline_constants']==28506 and a['constants']==s['constants']==12 and a['modules']==4 and a['duplicates']==a['conflicts']==0 and a['unresolved']==a['missing_seeds']==one(ex,'UNRESOLVED ')==[]
assert not any(l.startswith('UNSAFE_OR_PARTIAL ') for l in au)
ledger={};meta=W/'metadata';meta.mkdir();logs=W/'logs';logs.mkdir()
for label,attempt in [('export','sdk-selected-cut-export-v1'),('audit','sdk-selected-cut-audit-v2')]:
 d=E/attempt;r=json.loads((d/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0 and '-j1' in r['command'] and '-M4400' in r['command']
 ledger[attempt]={k:r[k] for k in ['target','exit_status','wall_seconds','peak_rss_bytes','swaps','source_sha256','print_axioms']}
 for f in ['source.lean','command.json','receipt.json','time.log']:shutil.copyfile(d/f,meta/(attempt+'-'+f))
 shutil.copyfile(d/'lean.log',logs/(attempt+'.log'))
# Preserve the exit-zero but POST-GATE REJECTED name-parsing diagnostic.
for f in ['source.lean','command.json','receipt.json','time.log','lean.log']:shutil.copyfile(E/'sdk-selected-cut-audit-v1'/f,meta/('EXCLUDED-sdk-selected-cut-audit-v1-'+f))
checks=[]
for row in pins['inputs']:
 for f in row['files']:
  p=Path(f['path']);checks.append(dict(path=str(p),unchanged=p.is_file() and sha(p)==f['sha256']))
assert all(r['unchanged'] for r in checks)
(P/'post-audit-inputs.json').write_text(json.dumps(dict(all_unchanged=True,files=checks),separators=(',',':'))+'\n')
basepaths=set()
for base in pins['bases']:
 d=Path(base['location']);assert sha(d/'manifest.json')==base['manifest_sha256']
 for f in base['files']:assert sha(d/f['relative'])==f['sha256'];basepaths.add(f['relative'])
newpaths={str(p.relative_to(W)) for p in (W/'transport').rglob('*.olean')}
fragments=dict(base_fragments=1428,new_fragments=4,extended_base_module_labels=sorted(newpaths&basepaths),rule='Read all THREE immutable locations as untrusted constant fragments; merge by full actual Name with strict declaration comparison. Do not overwrite a baseline module path and do not trusted-import raw files.')
(P/'fragment-consumption.json').write_text(json.dumps(fragments,indent=2)+'\n')
for p in P.glob('*.json'):shutil.copyfile(p,meta/p.name)
(W/'constants-incremental.jsonl').write_text('\n'.join(l[len('CONSTANT '):] for l in au if l.startswith('CONSTANT '))+'\n')
(W/'edges-incremental.jsonl').write_text('\n'.join(l[len('EDGE '):] for l in ex if l.startswith('EDGE '))+'\n')
(W/'README.txt').write_text('UNTRUSTED SECOND INCREMENTAL CURRENT SDK DATA\n12 new exact declarations in4 raw fragments, over the TWO immutable bases named in manifest.json. The source-selected semantic cut and complete S1/S6 original SDK consumers are included. Nine new SourceCuts projections support the complete record update.\nRaw imports/entries/extraConstNames empty; no env insertion or trusted logical declaration load. Exact Name values read from baseline raw files; printed-name parsing audit was rejected.\nThis is compositional DATA closure over previously checked immutable baselines, NOT kernel replay or original/current/ALL14/event/native/artifact/security closure. Retain all standing conditional premises.\nOne fragment extends existing SourceCuts module content: read BOTH, merge constants by exact Name after strict comparison, do NOT overwrite files or trusted-import raw parts. The base-only unsafe reserve auxiliary remains excluded from logical proof seeds.\n')
files=[dict(relative=str(p.relative_to(W)),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(W.rglob('*')) if p.is_file()]
bases=[{k:base[k] for k in ['location','manifest_sha256','constant_file','constant_file_sha256','constants','transport_modules']} for base in pins['bases']]
m=dict(schema='focused-extractor-proof-packet-v1',kind='second-incremental-untrusted-raw-declaration-transport',source_revision=pins['revision'],bases=bases,summary=a,combined_constants=28518,new_unsafe_or_partial=[],all_previous_selected_inputs_unchanged=True,ledger=ledger,fragment_consumption=fragments,files=files,scope='Raw exact-name graph closure of the new source-selected semantic-cut/S1 caller terms over immutable base data; no kernel reconstruction, native or artifact/security closure.')
(W/'manifest.json').write_text(json.dumps(m,indent=2)+'\n');mb=(W/'manifest.json').read_bytes()
for p in W.rglob('*'):
 if p.is_file():p.chmod(0o444)
for p in sorted([p for p in W.rglob('*') if p.is_dir()],key=lambda p:len(p.parts),reverse=True):p.chmod(0o555)
W.chmod(0o555);W.rename(dest)
(P/'release-manifest.json').write_bytes(mb);(P/'release.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',location=str(dest),manifest_sha256=hashlib.sha256(mb).hexdigest(),new_raw_bytes=sum(f['bytes'] for f in files if f['relative'].startswith('transport/')),summary=a,scope=m['scope']),indent=2)+'\n')
print(json.dumps(dict(location=str(dest),new_raw_bytes=sum(f['bytes'] for f in files if f['relative'].startswith('transport/')),summary=a)))
