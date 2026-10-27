"""Mechanical statement/source delta checks; does not invoke a compiler."""
from pathlib import Path
import hashlib,json,difflib
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def decl(name,start,end):
 s=(R/'lean'/f'{name}.lean').read_text();return s[s.index(start):s.index(end,s.index(start))].strip()
checks={}
for name,child in [('Literal','Finish'),('Cont','Literal'),('Caller','Cont'),('Result','Caller')]:
 old=decl('FIs_'+name,'def Outcome','\ntheorem')
 new=decl('FJs_'+name,'def Outcome','\ntheorem').replace('FJs_'+child+'.Outcome','FIs_'+child+'.Outcome')
 checks[name+'_only_child']=old==new
old=decl('FIs_Finish','def Outcome','\ntheorem');new=decl('FJs_Finish','def Outcome','\ntheorem')
removed='    ∀ (pairing_S3_S5_S9 : FIs_Pair.Law (Port3_FinishStage.release finish) v p i.data)\n    (matches_S4_S7'
assert old.count(removed)==1
checks['Finish_only_pair_binder']=old.replace(removed,'    ∀ (matches_S4_S7')==new
old=decl('ARX_Root','theorem deployed',' := by');new=decl('FJs_Top','theorem deployed',' := by')
checks['Top_only_two_reduced_predicates']=old==new.replace('FJs_GlobalOwners.Owners','FIp_GlobalOwners.Owners').replace('FJs_Result.Outcome','FIs_Result.Outcome')
result=dict(checks=checks,all_pass=all(checks.values()),sources={n:sha(R/'lean'/f'{n}.lean') for n in ['ARX_Root','FJs_Top','FIs_Finish','FJs_Finish','FIp_GlobalOwners','FJs_GlobalOwners']})
(P/'FJs_source_comparison.json').write_text(json.dumps(result,indent=2)+'\n')
assert result['all_pass'],result
print(json.dumps(checks))
