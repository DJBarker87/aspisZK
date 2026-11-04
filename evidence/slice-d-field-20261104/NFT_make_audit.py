from pathlib import Path
import re,json,difflib
E=Path(__file__).resolve().parent;Q=E.parent/'slice-d-define-20261104'
mods=['NFT_ByteBits','NFT_Bytes','NFT_QBytes','NFT_WideNew','NFT_ReferenceEq']
roots=[]
for m in mods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1];roots +=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
(E/'NFT_ROOTS.json').write_text(json.dumps(roots,indent=1)+'\n');(E/'NFT_COMBINED_IMPORT.lean').write_text('\n'.join('import '+m for m in mods)+'\n'+'\n'.join('#print axioms '+r for r in roots)+'\n#print axioms AspisR1.RPx_Deployed.deployed\n')
s=(Q/'NFQ_Stage2Driver.lean').read_text();start=s.index('    if mode == "stage2proof0"');end=s.index('    else if mode == "fixtures"',start);chunks=[roots[i:i+5]for i in range(0,len(roots),5)]
code=''
for i,g in enumerate(chunks):code+=('    if'if i==0 else '    else if')+' mode == "proof'+str(i)+'" then\n      (#[`NFT_COMBINED_IMPORT], #['+', '.join('`'+r for r in g)+'])\n'
s2=s[:start]+code+s[end:];(E/'NFT_ProofDriver.lean').write_text(s2);(E/'NFT_DRIVER.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),s2.splitlines(True),fromfile='NFQ_Stage2Driver.lean',tofile='NFT_ProofDriver.lean')))
b=(Q/'NFQ_stage2_audit_batch.py').read_text().replace('NFQ_L050','NFT_L021').replace('NFQ_stage2_audit','NFT_final_audit').replace('NFQ_Stage2Driver','NFT_ProofDriver').replace('NFQ_native','NFT_native').replace("[f'stage2proof{i}' for i in range(5)]", "[f'proof{i}' for i in range("+str(len(chunks))+')]' )
(E/'NFT_final_audit_batch.py').write_text(b)
(E/'NFT_FIXTURE_PATHS.json').write_text(json.dumps(['/home/dombarker/project-offloads/codex-cx-slice-d-field-cache-20261104/fixtures'])+'\n')
(E/'NFT_WALKER_SOURCE.lean.txt').write_bytes((Q/'NFQ_WALKER_SOURCE.lean.txt').read_bytes())
p=E/'NFT_run.py';r=p.read_text();needle="(b/'NFT_objects'/{(target+'.olean')!r}).parent.mkdir(parents=True,exist_ok=True)";assert needle in r
r=r.replace(needle,needle+'''\nfor support in ['NFA_WALKER.c','NFA_MemoryLimit.c']:\n p=b.parent/'codex-cx-slice-d-define-20261104'/'NFQ_native'/support\n if p.exists():(b/'NFT_native'/support).write_bytes(p.read_bytes())''')
p.write_text(r)
print(len(roots),len(chunks))
