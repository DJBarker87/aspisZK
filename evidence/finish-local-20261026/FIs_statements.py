from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
# Identify the dedicated statement audit by its source snapshot.
ps=[p for p in E.glob('FIs_[0-9][0-9][0-9]') if (p/'sources/FIs_Statements.lean').exists()]
p=sorted(ps)[-1];log=(p/'stdout.log').read_text()
parts={}
for name,label in [('Rc9_Top.deployed','BEFORE'),('FIs_Top.deployed','AFTER'),('FIs_Nonvacuity.composed','NONVACUITY')]:
 start=log.index('@AspisR1.'+name+' :')
 nxt=re.search(r"\n(?:@AspisR1\.|'AspisR1\.)",log[start+1:]);end=start+1+nxt.start() if nxt else len(log)
 text=log[start:end].rstrip()+'\n';parts[label]=text;(E/('FIs_'+label+'.lean.txt')).write_text(text)
norm=lambda s:re.sub(r'\s+',' ',s).strip()
expected=parts['BEFORE'].replace('Rc9_Top.deployed','FIs_Top.deployed').replace('P2P_Result.Outcome','FIs_Result.Outcome')
assert norm(expected)==norm(parts['AFTER']),'Unexpected root statement difference'
(E/'FIs_statement-check.json').write_text(json.dumps(dict(audit=p.name,exact_substitutions=['Rc9_Top.deployed -> FIs_Top.deployed','P2P_Result.Outcome -> FIs_Result.Outcome'],all_other_quantifiers_hypotheses_carriers_events_constants_conclusions_unchanged=True),indent=2)+'\n')
print('Full root statements agree after exactly two declared name substitutions.')
