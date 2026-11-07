from pathlib import Path
import re,json,hashlib,shutil,difflib
E=Path(__file__).resolve().parent;P=E.parent/'tx1-observed3-20261110';latest={}
for f in sorted(E.glob('NNG_L[0-9][0-9][0-9]/receipt.json')):
 d=json.loads(f.read_text());m=d.get('module','');s=E/'NNG_generated'/(m.replace('.','/')+'.lean');snap=f.parent/'sources'/'NNG_generated'/(m.replace('.','/')+'.lean')
 if d.get('kind')=='lean' and d.get('exit_status')==0 and s.is_file() and snap.is_file() and s.read_bytes()==snap.read_bytes() and m.startswith('NNG_') and 'Driver' not in m and 'COMBINED' not in m:latest[m]=f
roots=[]
for m,f in latest.items():roots+=re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)",(f.parent/'stdout.log').read_text())
old=set(json.loads((E/'NNG_C087_AUDIT_ROOTS.json').read_text())['roots']) | set(json.loads((E/'NNG_C137_AUDIT_ROOTS.json').read_text())['roots']) | set(json.loads((E/'NNG_FOLD_AUDIT_ROOTS.json').read_text())['roots']) | set(json.loads((E/'NNG_C136_AUDIT_ROOTS.json').read_text())['roots'])
roots=sorted(set(n for n in roots if n.startswith('AspisR1.NNG_') and n not in old));candidate='AspisR1.NNG_Nonempty094.no_candidate';assert candidate in roots
roots.remove(candidate);groups=[[candidate]]+[roots[i:i+24]for i in range(0,len(roots),24)]
text='import NMQ_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in sorted(latest))+'\n#print axioms '+candidate+'\n'
(E/'NNG_S094_COMBINED.lean').write_text(text)
(E/'NNG_S094_AUDIT_ROOTS.json').write_text(json.dumps({'roots':[candidate]+roots,'groups':groups,'selected_receipts':{m:str(f.relative_to(E))for m,f in latest.items()},'excluded_already_audited_roots':sorted(old)},indent=1))
(E/'NNG_S094_AUDIT_MODULES.json').write_text(json.dumps([['NNG_S094_COMBINED']]*len(groups)))
a=(E/'NNG_C136_ProofDriver.lean').read_text();b=a.replace('NNG_C136_','NNG_S094_');(E/'NNG_S094_ProofDriver.lean').write_text(b);(E/'NNG_S094_DRIVER.diff').write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True))))
(E/'NNG_S094_link.py').write_text((E/'NNG_C136_link.py').read_text().replace('NNG_C136_','NNG_S094_'))
(E/'NNG_S094_audit_batch.py').write_text((E/'NNG_C136_audit_batch.py').read_text().replace('NNG_C136_','NNG_S094_').replace('NNG_C136_audit','NNG_S094_audit'))
pins={n:hashlib.sha256((E/n).read_bytes()).hexdigest()for n in ['NNG_S094_AUDIT_ROOTS.json','NNG_S094_AUDIT_MODULES.json','NNG_native/NFA_WALKER.c','NNG_native/NFA_MemoryLimit.c']};(E/'NNG_S094_AUDIT_MANIFEST_PINS.json').write_text(json.dumps(pins,indent=1));print(json.dumps({'modules':len(latest),'new_roots':len(roots)+1,'groups':len(groups)}))
