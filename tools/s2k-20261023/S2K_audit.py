"""Audit receipts and exact source cuts; no prover replay."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2k-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(E.glob('*/receipt.json')):
 x=json.loads(p.read_text());kind=x['kind'];assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0'
 for f,h in x['source_hashes'].items():assert sha(p.parent/'sources'/f)==h,(p,f)
 assert x['source_revision'] and x['deps_fingerprint'] and x['command']
 assert x['wall_seconds']>=0 and int(x['peak_rss_kib'])>0
 if kind=='lean' and x['exit_status']==0:
  assert x['print_axioms']
  assert all('sorryAx' not in line and ('axioms:' in line or 'does not depend on any axioms' in line) for line in x['print_axioms'])
  for line in x['print_axioms']:
   if 'does not depend on any axioms' in line:continue
   names=line.split('[')[1].rstrip(']').split(', ');assert set(names)<= {'propext','Classical.choice','Quot.sound'}
 if kind=='kani':
  log=(p.parent/'stdout.log').read_text()
  if x['exit_status']==0:assert 'profile [optimized]' in log
  assert x['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  if x['exit_status']==0:assert 'VERIFICATION:- SUCCESSFUL' in log
 rows.append(dict(path=str(p.relative_to(E)),sha256=sha(p),kind=kind,attempt=x['attempt'],exit=x['exit_status']))
assert len([r for r in rows if r['kind']=='lean'])<=100
assert len([r for r in rows if r['kind']=='kani'])<=60
assert len([r for r in rows if r['kind']=='audit'])>=1
cuts=json.loads((E/'source-cuts.json').read_text())
for f,c in cuts.items():
 text=(R/c['source']).read_text();assert sha(R/c['source'])==c['source_sha256'];assert c['cut'] in text
 assert hashlib.sha256(c['cut'].encode()).hexdigest()==c['cut_sha256']
 assert c['cut'] in (E/'S2K-native'/f).read_text()
ctor=cuts['src/S2K_construct.rs']['cut']
assert ctor in (R/'programs/aspis-verifier/src/v7_pair_forest_dispatch.rs').read_text()
assert sha(D/'lean/S2K_Serialization.lean')==json.loads((E/'lean-002/receipt.json').read_text())['source_hashes']['S2K_Serialization.lean']
for f,c in json.loads((E/'native-source.json').read_text()).items():assert sha(R/f)==c['sha256']
# Every concrete consumer uses exactly the independently checked callee.
def copy32_body(text):
 return text[:text.index('#[kani::proof_for_contract(S2K_copy32)]')]
reference=copy32_body((E/'kani-009/sources/S2K-native/src/S2K_concrete.rs').read_text())
assert copy32_body((E/'S2K-native/src/S2K_concrete.rs').read_text())==reference
for level in range(20):
 attempt=E/f'kani-{10+level:03}'
 r=json.loads((attempt/'receipt.json').read_text());assert r['exit_status']==0
 text=(attempt/'sources/S2K-native/src/S2K_concrete.rs').read_text()
 assert copy32_body(text)==reference
 start=48+32*level
 section=text.split(f'fn S2K_frontier_level_{level:02}() {{',1)[1].split('\n}',1)[0]
 assert f'S2K_copy32(&mut output[{start}..{start+32}],&source,j,expected);' in section
 assert f'assert_eq!(output[{start}+j],(node[j/4].0 >> (8*(j%4))) as u8);' in section
 assert 'assert_eq!(output[i],before);' in section
 assert f'kani::assume(i<{start} || i>={start+32});' in section
assert json.loads((E/'kani-030/receipt.json').read_text())['exit_status']==0
assert 'stub_verified(S2K_encode_status)' not in (E/'S2K-native/src/lib.rs').read_text()
assert json.loads((E/'kani-031/receipt.json').read_text())['exit_status']==0
for n in [32,33,34]:
 assert 'CBMC timed out' in (E/f'kani-{n:03}/stdout.log').read_text()
h=json.loads((E/'host-audit.json').read_text());assert h['native_sources_all_match'];assert h['inherited_selected_objects']['all_match'];assert not h['own_remaining_processes']
changed=subprocess.check_output(['git','diff','--name-only','4af6a0f6bf'],cwd=R,text=True).splitlines()
assert all(f.startswith(('tools/s2k-20261023/','docs/research/100bit-spend-path-20261013/evidence/s2k-20261023/')) or f.startswith('docs/research/100bit-spend-path-20261013/lean/S2K_') or f in ['docs/research/100bit-spend-path-20261013/lean/S2K_Serialization.lean','docs/research/100bit-spend-path-20261013/design/S2K-20261023.md'] for f in changed),changed
x=dict(schema='focused-extractor-proof-packet-v1',branch='codex/cx-s2k-20261023',receipts=rows,budget=dict(lean_attempts=sum(r['kind']=='lean' for r in rows),lean_cap=100,kani_runs=sum(r['kind']=='kani' for r in rows),kani_cap=60),redundant=['lean-070'],accepted_lean=[r['attempt'] for r in rows if r['kind']=='lean' and r['exit']==0 and r['attempt']!='lean-070'],accepted_kani=[r['attempt'] for r in rows if r['kind']=='kani' and r['exit']==0],excluded=[r['attempt'] for r in rows if r['exit']!=0],status='PARTIAL: emit success unclosed; ASQ8 and TX2 unstarted',shipped_source_changed=False,elf_pins='inherited only; no rebuild triggered',new_trust=False)
(E/'manifest.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(audit='PASS',receipts=len(rows),budget=x['budget'])))
