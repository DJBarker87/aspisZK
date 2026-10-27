from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent;R=E.parents[1];L=R/'lean'
def top(name):
 s=(L/(name+'.lean')).read_text();s=s[s.index('theorem deployed'):];return s[:s.index(':= by')].strip()
def definition(name,decl):
 s=(L/(name+'.lean')).read_text();s=s[s.index('def '+decl):]
 for marker in ['\ntheorem ','\n#print axioms','\nend AspisR1.']:
  if marker in s:s=s[:s.index(marker)]
 return s.strip()
before=top('ARX_Root');after=top('FJp_Top')
canon=after.replace('FJp_GlobalOwners.Owners','FIp_GlobalOwners.Owners').replace('FJp_Result.Outcome','FIs_Result.Outcome')
assert canon==before,'Unexpected root binder/carrier/conclusion change'
checks=[]
for new,old,a,b in [('FJp_Result','FIs_Result','FJp_ActualCaller.Outcome','FIs_Caller.Outcome'),('FJp_ActualCaller','FIs_Caller','FJp_ActualCont.Outcome','FIs_Cont.Outcome'),('FJp_ActualCont','FIs_Cont','FJp_NativeLiteral.Outcome','FIs_Literal.Outcome'),('FJp_NativeLiteral','FIs_Literal','FJp_Finish.Outcome','FIs_Finish.Outcome')]:
 x=definition(new,'Outcome').replace(a,b);y=definition(old,'Outcome');assert x==y,new
 checks.append(dict(new=new,old=old,change=f'{b} -> {a}',otherwise_byte_identical=True))
old=definition('FIs_Finish','Outcome');new=definition('FJp_Finish','Outcome')
line='    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))\n'
assert old.count(line)==1
assert old.replace(line,'')==new,'Unexpected native finish change'
old=definition('FIp_Remaining','Holds');new=definition('FJp_Remaining','Holds')
line='  (∀ j,MatchingSupport.match0 input.data (q j)) ∧\n'
assert old.count(line)==1
assert old.replace(line,'')==new,'Unexpected global owner family change'
assert definition('FJp_GlobalOwners','Owners').replace('FJp_Remaining.Holds','FIp_Remaining.Holds')==definition('FIp_GlobalOwners','Owners')
assert all(hashlib.sha256((R/p).read_bytes()).hexdigest()==h for p,h in json.loads((E/'FJp_before-source-pins.json').read_text()).items())
(E/'FJp_before.lean.txt').write_text(before+'\n');(E/'FJp_after.lean.txt').write_text(after+'\n')
(E/'FJp_statement-check.json').write_text(json.dumps(dict(before='AspisR1.ARX_Root.deployed',after='AspisR1.FJp_Top.deployed',complete_source_types=True,focused_kernel_receipts_required=True,root_changes=['finishOwners removes F3Y_G_L143','native Outcome removes L143'],otherwise_byte_identical_after_exact_name_substitution=True,nested_outcomes=checks,old_sources_unchanged=True,retention_fact_does_not_escape='RootBinding' not in after,matching_implementation_law_not_a_top_argument='FJp_GlobalOwners.Matching' not in after),indent=2)+'\n')
print('Root and all five nested native outcome comparisons pass; exactly two atomic families removed.')
