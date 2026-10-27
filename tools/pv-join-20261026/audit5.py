from pathlib import Path
import json,re,hashlib,subprocess
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'evidence/pv-join-20261026/resume5'
old=json.loads((e.parent/'resume4/combined-audit-manifest.json').read_text())
receipts=[json.loads(f.read_text()) for f in sorted(e.glob('38*-receipt.json'))]
latest={x['module']:x for x in receipts}
sources=[];new_names=[]
for f in sorted(p.glob('PV_Join_*5*.lean')):
 if 'Audit5' in f.name:continue
 s=f.read_text();module='R1Z.'+f.stem;sha=hashlib.sha256(f.read_bytes()).hexdigest()
 if module.replace('.','/') not in latest:
  assert subprocess.run(['git','cat-file','-e','8eba145a71:'+str(f.relative_to(r))],capture_output=True).returncode==0,module
  continue
 q=latest[module.replace('.','/')];assert q['validation_exit']==0 and q['source_sha256']==sha,(module,'stale or failed')
 ns=re.search(r'^namespace\s+(\S+)',s,re.M);ns=ns[1] if ns else None
 names=[]
 for m in re.finditer(r'^#print axioms (\S+)',s,re.M):
  n=m[1];n=n if n.startswith(('R1Z.','PV_Join_Direct5Source.')) else (ns+'.'+n if ns else n)
  names.append(n);new_names.append(n)
 sources.append(dict(module=module,sha256=sha,theorems_or_functions=names,receipt_attempt=q['attempt']))
names=sorted(set(old['theorems']+new_names));head=old['headline']
imports=sorted(x['module'] for x in sources if x['theorems_or_functions'])
for suffix,part in [('A',names[:len(names)//2]),('B',names[len(names)//2:])]:
 text='import R1Z.PV_Join_CombinedAudit4\n'+''.join('import '+m+'\n' for m in imports)+'\n'
 text+=''.join('#print '+n+'\n#print axioms '+n+'\n' for n in part)
 (p/f'PV_Join_FinalAudit5{suffix}.lean').write_text(text)
text='import R1Z.PV_Join_FinalAudit5A\nimport R1Z.PV_Join_FinalAudit5B\n\n'+''.join('#print axioms '+n+'\n' for n in names+[head])
(p/'PV_Join_CombinedAudit5.lean').write_text(text)
x=dict(theorems_or_functions=names,headline=head,sources=sources,inherited_manifest='../resume4/combined-audit-manifest.json',new_print_names=sorted(set(new_names)),final_targets=['R1Z.PV_Join_FinalAudit5A','R1Z.PV_Join_FinalAudit5B','R1Z.PV_Join_CombinedAudit5'],kind='focused audit against retained cache; not a clean release manifest replay')
(e/'combined-audit-manifest.json').write_text(json.dumps(x,indent=2)+'\n')
print(len(names),'PV_Join proof/function declarations plus headline;',len(set(new_names)),'new printed names')
