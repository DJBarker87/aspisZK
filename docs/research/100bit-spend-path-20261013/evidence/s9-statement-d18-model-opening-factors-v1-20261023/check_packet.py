from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert m['schema']=='focused-extractor-proof-packet-v1' and not m['compiled_objects_included']
for f in m['files']:
 p=r/f['path'];assert p.is_file() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256'],p
assert {x['path'] for x in m['files']}=={str(p.relative_to(r)) for p in r.rglob('*') if p.is_file() and p.name!='manifest.json'}
ts={t['module']:t for t in m['targets']};assert len(ts)==1;edges=0
for t in ts.values():
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 assert t['peak_aggregate_rss_bytes']<8*1024**3 and sha(r/t['source'])==t['source_sha256']
 d=r/'proof'/t['label'];pre=json.loads((d/'preflight.json').read_text());rec=json.loads((d/'receipt.json').read_text())
 assert pre['source_sha256']==t['source_sha256'] and rec['object_sha256']==t['object_sha256']
 assert pre['limits']['lean_memory_mb']==4400 and pre['limits']['threads']==1 and pre['no_dependency_builds']
 assert pre['profile_sha256']==sha(d/'profile.txt')
 for mod,pin in pre['direct_imports'].items():
  if mod in ts:assert pin['sha256']==ts[mod]['object_sha256'];edges+=1
 log=(d/'lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 ax={n:[a.strip() for a in aa.split(',')] for n,aa in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)};ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",log)})
 assert ax==t['axioms'] and ax
 for aa in ax.values():assert set(aa)<={'propext','Classical.choice','Quot.sound'}
for p in r.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.so','.dylib','.o','.a','.pyc'}
other=json.loads((r/m['external_opening_packet']/'manifest.json').read_text())
op=next(t for t in other['targets'] if t['module']==m['external_opening_module'])
assert op['object_sha256']==m['external_opening_object_sha256']
p=json.loads((r/'proof/bridge/preflight.json').read_text())
assert p['direct_imports'][op['module']]['sha256']==op['object_sha256']
sel=json.loads((r/'overlays/combined-selection.json').read_text())
assert len(sel['project_objects'])==489
for mod,pin in p['direct_imports'].items():assert sel['project_objects'][mod]['sha256']==pin['sha256']
for pin in sel['project_objects'].values():assert not pin['builtin'] and len(pin['sha256'])==64
for pin in sel['companions']:assert '.so' not in pin['path'] and len(pin['sha256'])==64
assert 'Nat.Usize' in (r/'history/implicit-Usize-kind/lean.log').read_text()
print('PASS:1 focused target, existing openingPoints/D18/index helpers reused with pinned imports; exact logical pair bits, standard axioms. Full constructor/runtime/S9/security OPEN.')
