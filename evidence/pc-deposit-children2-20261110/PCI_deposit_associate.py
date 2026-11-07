from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
row=next(r for r in json.loads((E/'PCI_SOURCE_MAP.json').read_text()) if r['id']=='POOL:277')
s=(E/'PCI_DepositFission.rs').read_text()
# This negative-only branch is an intentionally wrong argument, never the passing copy.
s=re.sub(r'\s*#\[cfg\(PCI_DEPOSIT_ARG_MUTANT\)\]\s*let owner_key_bytes = salt_bytes;', '',s)
frozen=row['frozen_function'];body=frozen[frozen.index('{')+1:frozen.rindex('}')]
copy=s[s.index('{')+1:s.rindex('}')]
copy=copy.replace('INSTRUCTION_PAYLOAD_OFFSET..logical_len','INSTRUCTION_PAYLOAD_OFFSET..').replace('logical_len','bytes.len()')
norm=lambda x:re.sub(r'\s+','',x)
assert norm(copy)==norm(body),'body mismatch'
for bad in [copy.replace('WrongLength','WrongMagic',1),copy.replace('owner_key_bytes)','salt_bytes)',1)]:assert norm(bad)!=norm(body)
record=dict(row='POOL:277',frozen_function_sha256=row['full_function_sha256'],fission_sha256=hashlib.sha256((E/'PCI_DepositFission.rs').read_bytes()).hexdigest(),body_exact_after_whitespace=True,transforms=['slice metadata length to usize word','valid592-byte storage projection','payload suffix truncated at logical slice end'],negative_only_branch='PCI_DEPOSIT_ARG_MUTANT erased only for positive-body diff',controls=['wrong Err arm rejected','wrong owned argument rejected'],classification='ReviewedTranscription option A, plus borrow-minimal reference extraction under av; not trust removal')
f=E/'PCI_ASSOCIATIONS.json';records=json.loads(f.read_text());records=[r for r in records if r.get('row')!='POOL:277'];records.append(record);f.write_text(json.dumps(records,indent=1)+'\n')
print('PCI277 body diff and two mutation controls pass')
