from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
listed=set()
for f in m['files']:
 p=r/f['path'];assert p.is_file() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256'];assert f['path'] not in listed;listed.add(f['path'])
assert listed=={str(p.relative_to(r)) for p in r.rglob('*') if p.is_file() and p.name!='manifest.json'}
assert m['exit_status']==0 and m['process_swaps']==0 and m['watchdog_abort'] is None and m['peak_aggregate_rss_bytes']<8*1024**3
assert sha(r/m['source'])==m['source_sha256']
p=json.loads((r/'proof/preflight.json').read_text());rec=json.loads((r/'proof/receipt.json').read_text());assert rec['source_sha256']==m['source_sha256'] and rec['object_sha256']==m['object_sha256']
assert p['source_sha256']==m['source_sha256'] and p['limits']['lean_memory_mb']==4400 and p['limits']['threads']==1 and p['no_dependency_builds']
assert sha(r/'proof/profile.txt')==p['profile_sha256']
log=(r/'proof/lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
ax=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S);empty=re.findall(r"'([^']+)' does not depend on any axioms",log);assert len(ax)+len(empty)==2
assert ({n:[a.strip() for a in aa.split(',')] for n,aa in ax}|{n:[] for n in empty})==m['axioms']
for _,aa in ax:assert {a.strip() for a in aa.split(',')}<={'propext','Classical.choice','Quot.sound'}
owner=json.loads((r/'proof/namespace-owner-manifest.json').read_text());assert len(owner['selection'])==65 and len(owner['different_hash_shadowed_candidates'])==20
assert 'first-owner precedence preserved' in owner['scope']
for tag in ['v1-environment','v2-symbolic-fallback-needed']:
 assert 'error:' in (r/'history'/tag/'lean.log').read_text()
for f in r.rglob('*'):
 if f.is_file():assert f.suffix not in {'.olean','.ilean','.ir','.llbc','.pyc','.so','.dylib','.o','.a'}
print('PASS: retained wrapper canonical coordinate theorem; focused standard axioms; exact source/cache provenance; failed predecessors retained; current Rust source binding OPEN.')
