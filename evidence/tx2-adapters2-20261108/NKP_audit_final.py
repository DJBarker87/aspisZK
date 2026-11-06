from NKP_formal import *
subprocess.run([sys.executable,str(E/'NKP_audit_prepare.py')],check=True)
rc=run('NKP_L021','lean','NKP_COMBINED_IMPORT');assert rc['exit_status']==0
extra={'NIS_AUDIT_ROOTS.json':(E/'NKP_AUDIT_ROOTS.json').read_text(),'NIM_AUDIT_MODULES.json':json.dumps([['NKP_COMBINED_IMPORT']]),'NKP_EXPECTED_IMPORTS.jsonl':(E/'NKP_EXPECTED_IMPORTS.jsonl').read_text(),'NKP_audit_one.py':(E/'NKP_audit_one.py').read_text()}
binary='/home/dombarker/project-offloads/codex-cx-tx2-decoders2-20261107/NJQ_native/NJQ_RetainedProofDriver';h='82898d45b249439ff7c1c6ed03b4c5c49d72888643aadc82896987c668613c76'
# L008 fixtures are reused: identical byte-pinned binary and unchanged fixture
# objects. Only the proof module/root lists changed. No unchanged fixture replay.
rc=run('NKP_L022','audit','proof0',['python3','NKP_audit_one.py',binary,'proof0',h],extra=extra);assert rc['exit_status']==0
scan=json.loads((E/'NKP_SCAN_BINARY.json').read_text())
rc=run('NKP_L023','audit','scan',['python3','NKP_audit_one.py','NKP_native/NKP_ScanDriver','scan',scan['sha256']],extra={'NKP_EXPECTED_IMPORTS.jsonl':(E/'NKP_EXPECTED_IMPORTS.jsonl').read_text(),'NKP_audit_one.py':(E/'NKP_audit_one.py').read_text()});assert rc['exit_status']==0
rc=run('NKP_L024','cache','NKP_CohortPins',['python3','NKP_pin.py'],extra={n:(E/n).read_text() for n in ['NKP_pin.py','NKP_PREDECESSOR_PINS.json']});assert rc['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});names=['NKP_CLOSURE_PINS.json','NKP_LOADED_scan.jsonl']+list(p.name for p in b.glob('NKP_binary_*.json'))
print(json.dumps({{n:(b/n).read_text() for n in names}}))
''');assert r.returncode==0
for n,t in json.loads(r.stdout).items():
 p=E/n
 if n.endswith('.jsonl') or n=='NKP_CLOSURE_PINS.json':p.with_name(p.name+'.xz').write_bytes(lzma.compress(t.encode()));p.with_name(p.name+'.sha256').write_text(sha(t.encode())+'\n')
 else:p.write_text(t)
print('SECOND_FINAL_COMBINED_AUDIT_COMPLETE',flush=True)
