"""Compile-free source provenance check; no launcher/build changes."""
from pathlib import Path
import re,json,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1];L=R/'lean'
selection=json.loads((P/'FIq_native-selection.json').read_text());original=(R/selection['source']).read_text()
def declarations(s):
 if 'namespace AspisR1SelectedMaskProbe\n' in s:s=s.split('namespace AspisR1SelectedMaskProbe\n',1)[1].split('\nend AspisR1SelectedMaskProbe')[0]
 elif 'namespace FIq_Native\n' in s:s=s.split('namespace FIq_Native\n',1)[1].split('\nend FIq_Native')[0]
 out={}
 for b in re.split(r'(?=^/-- )',s,flags=re.M):
  code=re.sub(r'/--.*?-/', '', b,flags=re.S)
  m=re.search(r'\b(?:def|impl_def|abbrev)\s+([^\s(:]+)',code)
  if m:out[m[1]]=code
 return out
def normal(s):
 s=re.sub(r'@\[.*?\]','',s,flags=re.S)
 return re.sub(r'\s+','',s)
old=declarations(original);new={}
for file in list(L.glob('FIq_Native[0-9]*.lean'))+[L/'FIq_CopyPrefix.lean']:
 for n,b in declarations(file.read_text()).items():
  assert n not in new,n
  new[n]=b
exceptions={'core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator':'obsolete trait fields removed; concrete fold/rev calls retained',
'pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS':'14 literal records factored into named definitions',
'pool_v1.pair_forest_semantic_terminal.composition_parts':'explicit decide on the Boolean amount guard'}
verified=[]
for n in selection['names']:
 assert n in new,n
 expected=old[n]
 if n=='core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator':
  a=expected.index('  fold :=');b=expected.index('\n}',a);expected=expected[:a]+expected[b:]
 elif n.endswith('.composition_parts'):expected=expected.replace('ok (amount >= i)','ok (decide (amount >= i))')
 if n.endswith('.constants.COPY_PATTERNS'):continue
 assert normal(expected)==normal(new[n]),n
 verified.append(n)
# The memory-failed table is normalized only by explicit literal substitution;
# do not normalize arithmetic recurrences or generated large numerals.
snapshot=(P/'FIq_029/sources/FIq_Native13.lean').read_text();a=snapshot.index('def pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS');b=snapshot.index('/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1]')
constant=snapshot[a:b];lets=dict(re.findall(r'let (\w+) := (Array.repeat \d+#usize \d+#u\d+)\n',constant));start=constant.index('Array.make 14#usize');rows=[];depth=0;at=None
for i,ch in enumerate(constant[start:]):
 if ch=='{':
  if depth==0:at=start+i
  depth+=1
 elif ch=='}':
  depth-=1
  if depth==0:
   row=constant[at:start+i+1]
   row=re.sub(r'\b(?:'+ '|'.join(sorted(lets,key=len,reverse=True))+r')\b',lambda m:'('+lets[m[0]]+')',row);rows.append(row)
assert len(rows)==14
current=(L/'FIq_CopyPatterns.lean').read_text()
for i,row in enumerate(rows):
 match=re.search(r'def pattern'+f'{i:02}'+r'\s*:.*?:=\s*(\{.*?\})(?=\n\n|\nend)',current,re.S)
 assert match and normal(match[1])==normal(row),i
assembly=new['pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS']
assert re.findall(r'pattern\d\d',assembly)==[f'pattern{i:02}' for i in range(14)]
out=dict(accepted=True,source=selection['source'],source_sha256=hashlib.sha256(original.encode()).hexdigest(),selected_declarations=len(selection['names']),verbatim_after_documented_normalization=len(verified),exceptions=exceptions,named_literal_rows=14,qualification='Source provenance only. Concrete standard-library operation models and source/extraction/ELF correspondence remain the P6 boundary; no numeric security or premise-removal credit.')
(P/'FIq_native-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
