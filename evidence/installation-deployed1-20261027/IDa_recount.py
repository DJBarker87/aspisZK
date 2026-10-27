"""Read-only ledger recount and complete printed-kernel substitution check."""
from pathlib import Path
import copy,hashlib,json,re
E=Path(__file__).resolve().parent; R=E.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,x): (E/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def norm(s): return re.sub(r'\s+',' ',s).strip()
baseline=json.loads((E/'IDa_BASELINE.json').read_text())
for p,h in baseline['files'].items(): assert sha(R/p)==h,p
log=(E/'IDa_004/stdout.log').read_text()
receipt=json.loads((E/'IDa_004/receipt.json').read_text()); assert receipt['exit_status']==0
assert 'error:' not in log
start=log.index('@AspisR1.ARX_Root.deployed')
mid=log.index('@AspisR1.IDa_Deployed.ARX_Deployed',start)
end=log.index('structure AspisR1.DrvC_Installation.Configuration',mid)
before,after=log[start:mid],log[mid:end]
assert all(x not in before+after for x in ['⋯','...','sorryAx'])
(E/'IDa_ARX_Root.BEFORE.lean.txt').write_text(before)
(E/'IDa_ARX_Deployed.AFTER.lean.txt').write_text(after)
expected=norm(before).replace('@AspisR1.ARX_Root.deployed','@AspisR1.IDa_Deployed.ARX_Deployed',1)
oldbinder='(c : AspisR1.DrvC_Installation.Configuration AspisR1.FIo_Install.W CoreError)'
newbinder='(missing : AspisR1.IDa_Deployed.Uninstalled CoreError)'
assert expected.count(oldbinder)==1
expected=expected.replace(oldbinder,newbinder)
expected=re.sub(r'\bc\b','(@AspisR1.IDa_Deployed.deployedConfiguration CoreError missing indexError reservation)',expected)
assert expected==norm(after)
save('IDa_STATEMENT-CHECK.json',dict(before_sha256=sha(E/'IDa_ARX_Root.BEFORE.lean.txt'),after_sha256=sha(E/'IDa_ARX_Deployed.AFTER.lean.txt'),complete_kernel_types_no_elisions=True,exact_printed_type_substitution=True,oldbinder=oldbinder,newbinder=newbinder,substitution='c := @AspisR1.IDa_Deployed.deployedConfiguration CoreError missing indexError reservation',other_type_changes=[],source_root_unchanged=True,proof='Direct application of ARX_Root.deployed, checked in IDa_002 and re-audited in IDa_004'))
old=json.loads((R/'evidence/recount12-20261027/Rc12_LEDGER_DELTA.json').read_text())['roots']['ARX_Root']
rows=copy.deepcopy(old['rows'])
for row in rows:
 k=row['id']
 effect='Retained with identical family, guards and witnesses; no premise discharged.'
 if k in ['L078','L079','L080']:
  effect='Retained extraction boundary, now indexed by explicitly selected partial source dictionary. Source/native/body/effect correspondence is NOT derived by code selection.'
 if k in ['L142','L143','L144','L145','L146'] or k.startswith('F3Y_G_L14'):
  effect='Retained independently counted native/global law. Installed finish/semantic bodies are fixed, but SAME operand value, canonicality and literal transport law remains unproved by specialization.'
 if k=='L154': effect='Identical issued-query budget for the same arbitrary adversary/native1/copy/allocator; no query restriction added or removed.'
 row['IDa_specialization_effect']=effect
 row['IDa_removed']=False

def count(rs): return {c:sum(x['classification']==c for x in rs) for c in 'TPGC'}
def totals(rs):
 return {s:count([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']} | {'deployment-inclusive non-alias':count([r for r in rs if r['scope']!='deployment alias']),'raw including alias':count(rs)}
assert totals(rows)==old['after']
finish_ids=[f'L{i}' for i in range(142,147)]+[f'F3Y_G_L{i}' for i in range(142,147)]
assert all(sum(r['id']==k and r['classification']=='P' for r in rows)==1 for k in finish_ids)
save('IDa_RECOUNT.json',dict(method='Rc12/Rc11 atomic law-family ledger: split conjunction leaves; preserve SAME existential witnesses, guards and slots; no Fin22 multiplication; native/global finish rows separate; returned facts/data not premises; deployment aliases excluded from distinct totals.',before_theorem='AspisR1.ARX_Root.deployed',after_theorem='AspisR1.IDa_Deployed.ARX_Deployed',baseline='evidence/recount12-20261027/Rc12_LEDGER_DELTA.json#roots.ARX_Root',before=totals(old['rows']),after=totals(rows),delta={k:0 for k in 'TPGC'},removed=[],added=[],reclassified=[],rows=rows,finish_family_ids=finish_ids,code_identity_facts=['selected_fields','terminal_fixed','finish_fixed','boundaries_fixed'],code_identity_ledger_removal=False,adoption=False,authoritative_ledger_edited=False,contract_edited=False))
print(json.dumps(dict(before=totals(old['rows']),after=totals(rows),delta='0T/0P/0G/0C',complete_kernel_substitution=True),indent=2))
