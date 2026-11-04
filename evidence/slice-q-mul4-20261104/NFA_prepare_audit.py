from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-mul3-20261103';A=E.parent/'axaudit2-20261102'
exports=json.loads((P/'NEV_OBJECT_EXPORTS.json').read_text());entries=[]
for ex in exports:
 a=ex['attempt'];receipt=json.loads((P/a/'receipt.json').read_text());assert receipt['exit_status']==0
 roots=[]
 for line in receipt['print_axioms']:
  m=re.match("'([^']+)' (?:depends on axioms:|does not depend on any axioms)",line)
  if m and ('NEV_' in m[1]):roots.append(m[1])
 if roots:entries.append(dict(module=ex['target'],roots=roots,source_attempt=a,source_sha256=ex['source_sha256'],object_sha256=ex['sha256']))
original=entries[43]
for root in original['roots']:
 entries.append({**original,'roots':[root],'split_from':43})
(E/'NFA_AUDIT_ROOTS.json').write_text(json.dumps(entries,indent=2)+'\n')
(E/'NFA_WALKER.lean').write_bytes((A/'NEP_WALKER.lean').read_bytes())
(E/'NFA_NEP_Driver.lean.txt').write_bytes((A/'NEP_Driver.lean').read_bytes())
s=(A/'NEP_Driver.lean').read_text().replace('import NEP_WALKER','import NFA_WALKER').replace('import Lean\n','import Lean\nimport NFA_MemoryLimit\n',1)
start=s.index('  let (modules, roots) :=');end=s.index('  let env ←',start)
choices=[]
for i,e in enumerate(entries):
 choices.append(('    if' if i==0 else '    else if')+' mode == "'+str(i)+'" then\n      (#['+'`'+e['module']+'], #['+', '.join('`'+r for r in e['roots'])+'])')
s=s.replace('  enableInitializersExecution','  NFA_MemoryLimit.set\n  initSearchPath (← findSysroot)\n  enableInitializersExecution')
start=s.index('  let (modules, roots) :=');end=s.index('  let env ←',start)
s=s[:start]+'  let (modules, roots) :=\n'+'\n'.join(choices)+'\n    else (#[], #[])\n'+s[end:]
# Reject unknown audit mode before importing any modules, fail closed.
s=s.replace('  let env ←','  if modules.isEmpty then\n    IO.eprintln "Unknown NFA audit mode"\n    return 3\n  let env ←',1)
(E/'NFA_Driver.lean').write_text(s)
(E/'NFA_DRIVER_PROVENANCE.json').write_text(json.dumps(dict(walker_sha256=hashlib.sha256((E/'NFA_WALKER.lean').read_bytes()).hexdigest(),driver_original_sha256=hashlib.sha256((A/'NEP_Driver.lean').read_bytes()).hexdigest(),changes=['module import name NEP_WALKER to NFA_WALKER','module/root selection only','unknown-mode rejection','explicit runtime memory threshold 7000 MiB'],algorithm_unchanged=True,credit='pending literal-driver interpretation'),indent=2)+'\n')
print(len(entries),'module groups',sum(len(e['roots']) for e in entries),'top theorem roots')
