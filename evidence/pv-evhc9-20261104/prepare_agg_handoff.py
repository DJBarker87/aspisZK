from pathlib import Path
import json
E=Path(__file__).resolve().parent;old=E.parent/'pv-evhc8-20261104'
s=(old/'sequence.py').read_text()
s=s.replace('E=Path(__file__).resolve().parent;os.chdir(E)', '''# Invoked only by the lead's future admitted agg16 scope. Never admits or launches.
assert len(sys.argv)==3, 'usage: AGG-SEQUENCE.py <fresh-output-directory> <source-revision>'
D=Path(__file__).resolve().parent
P=D.parent/'codex-pv-evhc8-20261104'
E=Path(sys.argv[1]).resolve();E.mkdir(exist_ok=False)
for n in ['PV_BR_FixtureConsumer.lean','PV_NER_Scan.lean','COMBINED-MANIFEST.jsonl','SCAN-ROOTS.json','EXPECTED-SCAN-MODULES.json','RAW-ROOTS.json','ALL-OBJECT-HASH-CHECKS.json','lakefile.toml','lake-manifest.json','lean-toolchain']:
 (E/n).write_bytes((P/n).read_bytes())
(E/'inputs').mkdir();(E/'inputs/NER_AXIOMS.json').write_bytes((P/'inputs/NER_AXIOMS.json').read_bytes())
os.chdir(E)''')
s=s.replace("read('AUTHORIZATION.json')['revision']","sys.argv[2]")
s=s.replace("base+['--run','NEP_Driver.lean']","base+['--run',str(D/'NEP_Driver.lean'),'final']")
(E/'AGG-SEQUENCE.py').write_text(s)
