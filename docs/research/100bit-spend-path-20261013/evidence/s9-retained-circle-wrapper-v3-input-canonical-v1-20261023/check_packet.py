from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent;repo=next(p for p in r.parents if (p/'.git').exists());m=json.loads((r/'manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert p.is_file() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256']
assert {f['path'] for f in m['files']}=={str(p.relative_to(r)) for p in r.rglob('*') if p.is_file() and p.name!='manifest.json'}
assert m['exit_status']==0 and m['process_swaps']==0 and m['watchdog_abort'] is None and m['peak_aggregate_rss_bytes']<8*1024**3
assert sha(r/m['source'])==m['source_sha256']
p=json.loads((r/'proof/preflight.json').read_text());rec=json.loads((r/'proof/receipt.json').read_text());assert rec['source_sha256']==m['source_sha256'] and rec['object_sha256']==m['object_sha256']
assert p['limits']['lean_memory_mb']==4400 and p['limits']['threads']==1 and p['no_dependency_builds']
assert sha(r/'proof/profile.txt')==p['profile_sha256']
ref=repo/m['reused_evidence']['path'];assert sha(ref)==m['reused_evidence']['sha256'];dep=json.loads(ref.read_text());assert p['direct_imports']['S9CircleWrapperOutputCanonicalV1']['sha256']==dep['object_sha256']
log=(r/'proof/lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
ax=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);empty=re.findall(r"'([^']+)' does not depend on any axioms",log);assert len(ax)+len(empty)==3
assert ({n:[a.strip() for a in aa.split(',')] for n,aa in ax}|{n:[] for n in empty})==m['axioms']
for _,aa in ax:assert {a.strip() for a in aa.split(',')}<={'propext','Classical.choice','Quot.sound'}
assert 'error(lean.unknownIdentifier)' in (r/'history/failed-v1-owner-name/lean.log').read_text()
for f in r.rglob('*'):
 if f.is_file():assert f.suffix not in {'.olean','.ilean','.ir','.llbc','.pyc','.so','.dylib','.o','.a'}
print('PASS: exact V3 canonical-input transport from retained wrapper calls; standard axioms; current Rust binding remains OPEN.')
