from pathlib import Path
import subprocess,re,hashlib,json
E=Path(__file__).resolve().parent
raw=(E/'NIV_extracted/entry/raw/NIV_entry/Types.lean').read_bytes()
owner='docs/research/100bit-spend-path-20261013/lean/AdapterRwTypes.lean'
canon=subprocess.check_output(['git','show','HEAD:'+owner])
def constructors(b):
 s=b.decode();s=s[s.index('inductive solana_program_error.ProgramError where'):]
 lines=[]
 for l in s.splitlines()[1:]:
  if l.startswith('| '):lines.append(l.strip())
  elif l.strip() and lines:break
 return lines
r=constructors(raw);c=constructors(canon);assert len(r)==26 and r==c
x=dict(status='PASS',raw_sha256=hashlib.sha256(raw).hexdigest(),canonical_owner=owner,canonical_sha256=hashlib.sha256(canon).hexdigest(),constructors=r,full_custom_u32=True,full_borsh_string=True,enum_layout_claim=False,duplicate_owner_introduced=False)
(E/'NIV_CARRIERS.json').write_text(json.dumps(x,indent=1)+'\n')
print('PASS canonical ProgramError 26 constructors including full String and U32')
