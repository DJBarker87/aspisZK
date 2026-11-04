from pathlib import Path
import json,hashlib,re,difflib
E=Path(__file__).resolve().parent
old=set(json.loads((E/'NFT_ROOTS.json').read_text()));roots=[];mods=[]
for p in sorted(E.glob('NFT_L???/receipt.json')):
 r=json.loads(p.read_text());m=r['module'];f=E/(m+'.lean')
 if r['exit_status']!=0 or not f.exists() or m in ['NFT_ProofDriver','NFT_COMBINED_IMPORT','NFT_Driver','NFT_STAGE2_IMPORT','NFT_Stage2Driver']:continue
 if hashlib.sha256(f.read_bytes()).hexdigest()not in r['source_hashes'].values():continue
 new=[s.split("'")[1]for s in r['print_axioms']if s.split("'")[1]not in old]
 if new and m not in mods:mods.append(m)
 for root in new:
  if root not in roots:roots.append(root)
assert len(roots)==58
(E/'NFT_STAGE2_ROOTS.json').write_text(json.dumps(roots,indent=1)+'\n')
(E/'NFT_STAGE2_IMPORT.lean').write_text('import NFT_COMBINED_IMPORT\n'+''.join('import '+m+'\n'for m in mods)+''.join('#print axioms '+r+'\n'for r in roots)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
s=(E/'NFT_ProofDriver.lean').read_text();start=s.index('    if mode == "proof0"');end=s.index('    else if mode == "fixtures"',start)
branches=''
for i in range((len(roots)+4)//5):
 branches+=('    if'if i==0 else '    else if')+' mode == "proof'+str(i)+'" then\n      (#[`NFT_STAGE2_IMPORT], #['+', '.join('`'+r for r in roots[i*5:(i+1)*5])+'])\n'
t=s[:start]+branches+s[end:];(E/'NFT_Stage2Driver.lean').write_text(t)
(E/'NFT_STAGE2_DRIVER.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='NFT_ProofDriver.lean',tofile='NFT_Stage2Driver.lean')))
s=(E/'NFT_final_audit_batch.py').read_text().replace('NFT_L021','NFT_L060').replace('NFT_final_audit','NFT_stage2_audit').replace('NFT_ProofDriver','NFT_Stage2Driver').replace('range(3)','range(12)')
(E/'NFT_stage2_audit_batch.py').write_text(s)
