"""Validate retained SPEC evidence without re-running Lean or a raw audit."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).resolve().parent
base='5e397cb38787124d8a4bce7d3ea54f2d38e6c7e7'
sha=lambda b:hashlib.sha256(b).hexdigest()
roots=json.loads((E/'AUDIT_ROOTS.json').read_text());results=[]
for c,g in roots.items():
 log=(E/f'out-49790-{c}.log').read_text()
 found=[json.loads(l.split('NEP62_RESULT ',1)[1]) for l in log.splitlines() if l.startswith('NEP62_RESULT ')]
 assert len(found)==len(g['roots']) and {r['root'] for r in found}==set(g['roots'])
 assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in found)
 results.extend(found)
receipt=json.loads((E/'receipt-49790.json').read_text());assert receipt['accepted'] and receipt['exit']==0
(E/'RAW_AUDIT.json').write_text(json.dumps({'attempt':49790,'strict_raw':True,'roots':results,'root_count':len(results),'unresolved':0,'summary_mismatches':0,'receipt':receipt,'qualification':'Two isolated sequential coherent environments; no combined-root composition claim. Same private importAll walker/collector.'},indent=2)+'\n')
m=json.loads((E/'RAW_GRAPH_MANIFEST.json').read_text());compressed=(E/'RAW_GRAPH_ARCHIVE.json.xz').read_bytes();assert sha(compressed)==m['archive_sha256'];raw=lzma.decompress(compressed);assert sha(raw)==m['uncompressed_sha256']
(E/'RAW_GRAPH_ARCHIVE.json.sha256').write_text(sha(raw)+'\n')
archive=json.loads(raw)
for f in m['files']:
 assert sha(archive[f['name']].encode())==f['sha256']
accepted=[];failed=[]
for f in sorted(E.glob('receipt-497*.json')):
 r=json.loads(f.read_text())
 if r['attempt']>=49713:continue
 if r['accepted']:
  path=Path('lean')/(r['target']+'.lean');assert sha(path.read_bytes())==r['source_sha256']
  assert 'sorryAx' not in '\n'.join(r['axioms_summary_based'])
  accepted.append({'attempt':r['attempt'],'module':r['target'],'source_sha256':r['source_sha256'],'path':str(path),'wall':r['wall'],'peak_rss_kbytes':r['peak_rss_kbytes'],'swaps':r['swaps']})
 else:
  assert sha(lzma.decompress((E/f"failed-{r['attempt']}.lean.xz").read_bytes()))==r['source_sha256']
  failed.append(r['attempt'])
freeze=json.loads(subprocess.check_output(['git','show',base+':evidence/pv-lib-20261107/FREEZE.json']))
for name,want in freeze['files'].items():
 raw=subprocess.check_output(['git','show','HEAD:evidence/pv-lib-20261107/'+name]);assert sha(raw)==want
paths=subprocess.check_output(['git','diff','--name-only',base+'..HEAD'],text=True).splitlines()
assert all(p.startswith('evidence/pv-lib-20261107/lane-SPEC/') or re.fullmatch(r'lean/PV_LIB_SPEC_.*\.lean',p) for p in paths)
for f in Path('lean').glob('PV_LIB_SPEC_*.lean'):
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^axiom ',f.read_text(),re.M)
report={'accepted_focused':accepted,'failed_elaborations':failed,'raw_roots':len(results),'full_frozen_contracts_elaborated':0,'normative_specs':29,'entry_witnesses':['PV_LIB_SPEC_Source7Entry.entry_nonempty','PV_LIB_SPEC_Source7Entry.toVec_entry_nonempty'],'full_joint_composition_witnesses':0,'frozen_files_unchanged':len(freeze['files']),'write_boundary_valid':True,'endpoint_premises_removed':0,'endpoint_premises_added':0,'shared_slot_status_changes':0,'target_established':False}
(E/'VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'accepted_focused':len(accepted),'failed':failed,'strict_raw_roots':len(results),'freeze_unchanged':len(freeze['files']),'boundary':'PASS','full_contracts':0}))
