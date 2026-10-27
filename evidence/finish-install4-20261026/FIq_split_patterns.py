from pathlib import Path
import re,json
P=Path('evidence/finish-install4-20261026');L=Path('lean')
s=(P/'FIq_029/sources/FIq_Native13.lean').read_text()
a=s.index('/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::constants::COPY_PATTERNS]')
b=s.index('/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1]')
head=s[:s.index('namespace FIq_Native')+len('namespace FIq_Native')]+ '\n'
(L/'FIq_CopyPrefix.lean').write_text(s[:a]+'\nend FIq_Native\n')
constant=s[a:b];lets=dict(re.findall(r'let (\w+) := (Array.repeat \d+#usize \d+#u\d+)\n',constant))
start=constant.index('Array.make 14#usize');rows=[];depth=0;at=None
for i,ch in enumerate(constant[start:]):
 if ch=='{':
  if depth==0:at=start+i
  depth+=1
 elif ch=='}':
  depth-=1
  if depth==0:
   row=constant[at:start+i+1]
   row=re.sub(r'\b(?:'+ '|'.join(sorted(lets,key=len,reverse=True))+r')\b',lambda m:'('+lets[m[0]]+')',row)
   rows.append(row)
assert len(rows)==14
out=head.replace('import FIq_Native12','import FIq_CopyPrefix')
for i,row in enumerate(rows):out+=f'\n@[irreducible] def pattern{i:02} : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=\n{row}\n'
out+='\nend FIq_Native\n';(L/'FIq_CopyPatterns.lean').write_text(out)
new=head.replace('import FIq_Native12','import FIq_CopyPatterns')+'''\n@[global_simps, irreducible]
def pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS :
    Array pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern 14#usize :=
  Array.make 14#usize ['''+','.join(f'pattern{i:02}' for i in range(14))+']\n\n'+s[b:]
(L/'FIq_Native13.lean').write_text(new)
(P/'FIq_patterns-split.json').write_text(json.dumps({'failure':'FIq_029','replacement':['FIq_CopyPrefix','FIq_CopyPatterns','FIq_Native13'],'change':'Factor each of 14 literal pattern records into a named irreducible definition; repeat initializers substituted literally. Same row order and scalar values; no large recurrence reduction.'},indent=2)+'\n')
