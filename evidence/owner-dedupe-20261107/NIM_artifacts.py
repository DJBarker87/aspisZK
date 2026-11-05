from pathlib import Path
import hashlib,json,lzma,subprocess
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();checked=0
for line in (E/'NIM_ATTEMPTS.jsonl').read_text().splitlines():
 r=json.loads(line)
 for n,h in r['source_hashes'].items():
  p=E/r['attempt']/'sources'/n;assert p.is_file()and H(p.read_bytes())==h,p;checked+=1
for p in E.glob('NIM_NEP_*_REACHABLE.txt.sha256'):
 z=p.with_name(p.name.removesuffix('.sha256')+'.xz');assert H(lzma.decompress(z.read_bytes()))==p.read_text().strip(),p;checked+=1
for row in json.loads((E/'NIM_PROVENANCE.json').read_text())['modules']:
 assert H((E/row['output']).read_bytes())==row['sha256'];assert H((E.parents[1]/row['source']).read_bytes())==row['source_sha256'];checked+=2
raw=lzma.decompress((E/'NIM_CLOSURE_PINS.json.xz').read_bytes());assert H(raw)==(E/'NIM_CLOSURE_PINS.json.sha256').read_text().strip();checked+=1
for p in E.rglob('*'):
 if p.is_file():
  assert p.stat().st_size<=20*1024*1024,p
  assert p.suffix not in ['.olean','.ir','.pyc','.elf'],p
assert not list(E.rglob('__pycache__'))
required=['NIM_DIAGNOSIS.md','NIM_PROVENANCE.json','NIM_COMBINED_IMPORT.lean','NIM_AUDIT.json','NIM_SCAN.json','NIM_LEDGER_DELTA.json','NIM_HANDOFF.md','NIM_REMAINING.md','NIM_ATTEMPTS.jsonl']
assert all((E/n).is_file()for n in required)
changed=subprocess.check_output(['git','diff','--name-only','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs','Cargo.lock'],text=True);assert not changed
print(json.dumps(dict(status='PASS',hash_checks=checked,required_outputs=required,shipped_tree_identical=True,full_object_pins=len(json.loads(raw)['selected_objects']))))
