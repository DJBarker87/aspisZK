from pathlib import Path
import json
E=Path(__file__).resolve().parent
s=Path('evidence/tx2-model2-20261106/NHT_run.py').read_text().replace('NHT','NHV').replace('codex-cx-tx2-model2-20261106','codex-cx-tx2-native-20261106')
s=s.replace('90 if kind', '120 if kind').replace('2 if kind','1 if kind')
a=s.index("elif kind=='kani':")
b=s.index("elif kind=='lean':",a)
s=s[:a]+'''elif kind=='kani':
 files['NHV_gate.py']=(E/'NHV_gate.py').read_text()
 for n,t in json.loads((E/'NHV_NATIVE_INPUTS.json').read_text()).items():files['NHV_src/'+n]=t
 files['NHV_SOURCE_PINS.json']=(E/'NHV_SOURCE_PINS.json').read_text()
 sources=list(files);command=['python3','NHV_gate.py',a+'.json']
'''+s[b:]
s=s.replace(" raise RuntimeError('NHV has zero Kani budget')\n",'')
s=s.replace("if os.environ.get('NHV_INVERT')", "if os.environ.get('NHV_INVERT')")
# One compiler job; timeout unchanged from predecessor. Budget uses separate K/L namespaces.
s=s.replace("timeout=180", "timeout=180")
(E/'NHV_run.py').write_text(s)
paths=json.loads(Path('evidence/tx2-model2-20261106/NHT_RESTORE_PATHS.json').read_text())
paths[0]='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHV_seed_20261106'
paths.insert(0,'/home/dombarker/project-offloads/codex-cx-tx2-native-20261106/NHV_objects')
(E/'NHV_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
s=Path('evidence/slice-d-prepare-20261104/NFW_gate.py').read_text().replace('NFW','NHV')
# Include complete per-crate features, not only the reached crate closure.
s=s.replace("selected_closure=[", "all_crate_features=[dict(name=pkgs[i]['name'],version=pkgs[i]['version'],source=pkgs[i].get('source'),features=nodes[i]['features']) for i in sorted(nodes)],selected_closure=[")
(E/'NHV_gate.py').write_text(s)
(E/'NHV_COMBINED_IMPORT.lean').write_text('import NHT_COMBINED_IMPORT\nimport NGK_COMBINED_IMPORT\n#check AspisR1.RPx_Deployed.deployed\n#print axioms AspisR1.RPx_Deployed.deployed\n')
