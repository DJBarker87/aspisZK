from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-pool-retdata-20261104'
code='''from pathlib import Path
import json,lzma,hashlib,base64
b=Path(B)
paths=[b/'NFO_LOADED.jsonl',*b.glob('NEP_final_*_REACHABLE.txt'),*b.glob('NEP_fixtures_*_REACHABLE.txt')]
out={str(p.relative_to(b)):p.read_text() for p in paths}
raw=json.dumps(out,sort_keys=True).encode();print(json.dumps(dict(sha256=hashlib.sha256(raw).hexdigest(),xz=base64.b64encode(lzma.compress(raw,preset=6)).decode())))
'''.replace('Path(B)',f'Path({B!r})')
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
import base64
o=json.loads(r.stdout);data=base64.b64decode(o['xz']);raw=lzma.decompress(data);assert hashlib.sha256(raw).hexdigest()==o['sha256']
(E/'NFO_AUDIT_ARTIFACTS.json.xz').write_bytes(data);(E/'NFO_AUDIT_ARTIFACTS.json.sha256').write_text(o['sha256']+'  NFO_AUDIT_ARTIFACTS.json\n')
archive=json.loads(raw);print('Collected',len(archive),'artifacts',len(data),'compressed bytes')
rows=[json.loads(s.split('NEP_RESULT ',1)[1]) for s in (E/'NFO_L040/stdout.log').read_text().splitlines() if 'NEP_RESULT ' in s]
fixtures=[r for r in rows if r['root'].startswith(('NEP_Planted.','NEP_Mutate'))];proofs=[r for r in rows if r not in fixtures]
assert len(fixtures)==8 and len(proofs)==len(json.loads((E/'NFO_ROOTS.json').read_text()))
loaded=[json.loads(l) for l in archive['NFO_LOADED.jsonl'].splitlines()]
failed=[r for r in loaded if r['dangling']]
(E/'NFO_SCAN.json').write_text(json.dumps(dict(status='FAIL',receipt='NFO_L043/receipt.json',modules=len(loaded),declarations=sum(r['declarations'] for r in loaded),edges=sum(r['edges'] for r in loaded),dangling_references=sum(len(r['dangling']) for r in loaded),modules_with_dangling=failed,own_modules=[r for r in loaded if r['module'].startswith('NFO_')],limitation='No independent baseline import comparison. Do not waive any dangling reference as harmless.'),indent=1)+'\n')
expected={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx']}
assert all(r['walked_axioms']==expected.get(r['root'],[]) and r['equal'] for r in fixtures)
standard={'propext','Classical.choice','Quot.sound'}
audit=dict(status='FAIL',reason='Five raw walker / collectAxioms disagreements; closure scan has650 dangling references.',walker=json.loads((E/'NFO_AUDIT_PINS.json').read_text()),driver_diff='NFO_DRIVER.diff',receipts=['NFO_L035/receipt.json','NFO_L036/receipt.json','NFO_L037/receipt.json','NFO_L038/receipt.json','NFO_L039/receipt.json','NFO_L040/receipt.json','NFO_L041/receipt.json','NFO_L042/receipt.json','NFO_L043/receipt.json'],fixtures=fixtures,fixtures_all_equal=all(r['equal'] for r in fixtures),fixtures_exact_expected=True,roots=proofs,all_walked_axioms_standard=all(set(r['walked_axioms'])<=standard for r in proofs),all_collect_axioms_standard=all(set(r['collect_axioms'])<=standard for r in proofs),mismatches=[r for r in proofs if not r['equal']],unresolved_audit_constants=0,coherence_scan='NFO_SCAN.json',artifact_sha256=o['sha256'],classification='Compiled conditional/support theorems only; aggregate ax2 and coherence gates FAILED; no release claim')
(E/'NFO_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
print('Audit roots',len(proofs),'mismatches',len(audit['mismatches']),'scan failures',sum(len(r['dangling']) for r in failed))
print('First scan failures',[(r['module'],len(r['dangling']),r['dangling'][:1]) for r in failed[:6]])
