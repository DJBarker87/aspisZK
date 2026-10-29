from auditlib9 import *
records=[]
for id in range(60600,60700):
 p=f'evidence/pv-rdcd3-20261028/lean-{id}/receipt.json';s=read('rw',p)
 if s is None:continue
 z=json.loads(s);ax=z.get('axioms',z.get('print_axioms',[]));ax='\n'.join(ax) if isinstance(ax,list) else ax;status=str(z.get('exit',z.get('exit_status')))
 records.append(dict(id=id,exit=status,sorryAx='sorryAx' in ax,axiom_reports=len(re.findall(r'depends on axioms|does not depend on any axioms',ax)),receipt=p))
 assert status!='0' or 'sorryAx' not in ax,p
assert len(records)==100
out=dict(lean_receipts=len(records),failed=[r for r in records if r['exit']!='0'],failed_sorryAx=[r['id'] for r in records if r['sorryAx']],credited_sorryAx=[],records=records)
(P/'failed-attempt-audit9.json').write_text(json.dumps(out,indent=1)+'\n');save();print('Rdcd3 all100 receipts checked; failures',len(out['failed']),'sorryAx only in',len(out['failed_sorryAx']),'failed receipts')
