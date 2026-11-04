"""Receipt-only final lane verification; never reruns a proof or changes sources."""
from pathlib import Path
import json,hashlib,collections,subprocess
E=Path(__file__).resolve().parent
entries=[json.loads(l) for l in (E/'NFR_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({d['attempt'] for d in entries})==len(entries)
counts=collections.Counter(d['kind'] for d in entries)
used=dict(kani=counts['kani'],lean=sum(v for k,v in counts.items() if k not in ['kani','extract']),extract=counts['extract'])
assert used==dict(kani=70,lean=60,extract=2),used
for d in entries:
 if d['kind']!='kani':continue
 a=d['attempt'];g=json.loads((E/(a+'-graph-check.json')).read_text());l=json.loads((E/(a+'-lock-check.json')).read_text());s=json.loads((E/(a+'-source-check.json')).read_text());r=json.loads((E/(a+'-rule16-check.json')).read_text())
 assert g['graph_matches_frozen'] and not g['edge_errors'] and l['unchanged'] and not s['errors'] and r['no_writable_static'],a
 assert d['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
splits=[json.loads(l) for l in (E/'NFR_C_SPLIT_CAMPAIGN.jsonl').read_text().splitlines()]
controls=[json.loads(l) for l in (E/'NFR_C_EDGE_CONTROLS.jsonl').read_text().splitlines()]
assert len(splits)==18 and all(not d['timeout'] and not d['unwind'] and d['exit']==(1 if d['mode'].endswith('negative') else 0) for d in splits)
assert len(controls)==9 and all(d['matched'] for d in controls)
audit=json.loads((E/'NFR_AUDIT.json').read_text());assert audit['new_roots']==69 and audit['new_root_unresolved']==0 and audit['new_module_unresolved']==0
inherited=json.loads((E/'NFR_INHERITED_INCOHERENCE.json').read_text());assert inherited['total_unresolved']==650 and len(inherited['modules'])==15
assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*') if p.is_file())
assert not list(E.rglob('__pycache__'))
assert not subprocess.check_output(['git','diff','--name-only','5b21a44bf40','--','crates','programs'],text=True).strip()
out=dict(used=used,attempts=len(entries),native_split_passes=9,native_split_failing_controls=9,additional_failing_controls=9,raw_roots=69,new_module_unresolved=0,inherited_unresolved=650,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),ledger_sha256=hashlib.sha256((E/'NFR_ATTEMPTS.jsonl').read_bytes()).hexdigest(),formal_release=False,composed_rows_closed=0)
(E/'NFR_FINAL_CHECK.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
