"""Final combined closure; unchanged raw driver prefix/action; separate scanner."""
from pathlib import Path
import json,re,difflib,hashlib,subprocess
E=Path(__file__).resolve().parent
exec((E/'NFS_prepare.py').read_text(),{'__file__':str(E/'NFS_prepare.py')})
a=json.loads((E/'NFS_AUDIT_ROOTS.json').read_text());a['modules']+=['NFS_PacketRoot','NFS_QueryLoopRoot','NFS_LoopTrace']
roots=a['roots'][:]
newmods=['NFS_AccumDomain','NFS_AccumInstall','NFS_QueryOps','NFS_QueryBack','NFS_FoldInstall','NFS_TraceBack','NFS_DotTrace','NFS_QueryValuesPacket','NFS_ReadCanonical','NFS_QueryInvariant','NFS_CallerDomains','NFS_QueryLoopRoot','NFS_LoopTraceDefs','NFS_LoopTrace','NFS_PacketRoot']
a['modules']=list(dict.fromkeys(a['modules']+newmods))
for m in newmods:
 s=(E/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 roots += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
roots += json.loads((E.parent/'slice-q-values-20261104/NFP_AUDIT_ROOTS.json').read_text())['roots']
roots=list(dict.fromkeys(roots));a.update(roots=roots,groups=[roots[i:i+4] for i in range(0,len(roots),4)],new_modules=newmods)
(E/'NFS_AUDIT_ROOTS.json').write_text(json.dumps(a,indent=1)+'\n')
(E/'NFS_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in a['modules'])+''.join('#print axioms '+r+'\n' for r in roots))
s=(E.parent/'slice-q-phase-20261104/NFN_ProofDriver.lean').read_text();begin=s.index('    if mode == "proof0" then');end=s.index('    else if mode == "fixtures" then',begin)
select=''
for i,rs in enumerate(a['groups']):select+=('    if' if i==0 else '    else if')+f' mode == "proof{i}" then\n      (#[`NFS_COMBINED_IMPORT], #['+', '.join('`'+r for r in rs)+'])\n'
driver=s[:begin]+select+s[end:];(E/'NFS_ProofDriver.lean').write_text(driver)
(E/'NFS_PROOF_DRIVER.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),driver.splitlines(True),fromfile='NFN_ProofDriver.lean',tofile='NFS_ProofDriver.lean')))
raw_action=s[s.index('  let ctx : Command.Context'):];assert driver[driver.index('  let ctx : Command.Context'):]==raw_action
assert driver[:driver.index('/-- Standalone runtime')]==s[:s.index('/-- Standalone runtime')]
x=json.loads((E/'NFS_AX2_CONFORMANCE.json').read_text());x.update(driver_source_sha256=hashlib.sha256(driver.encode()).hexdigest(),prefix_unchanged=True,raw_action_unchanged=True,fixture_target='NFS_L086');(E/'NFS_AX2_CONFORMANCE.json').write_text(json.dumps(x,indent=1)+'\n')
g={r['module']:r['imports'] for r in map(json.loads,(E/'NFS_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
for p in E.glob('NFS_*.lean'):g[p.stem]=list(dict.fromkeys(['Init']+[m for l in p.read_text().splitlines() if l.startswith('import ') for m in l[7:].split() if m!='all']))
(E/'NFS_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=im))+'\n' for n,im in sorted(g.items())))
print('final raw roots',len(roots),'groups',len(a['groups']))
