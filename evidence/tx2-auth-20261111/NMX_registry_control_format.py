from pathlib import Path
import re,json,sys
E=Path(__file__).resolve().parent;p=E/(sys.argv[1] if len(sys.argv)>1 else 'NMX_R3_RegistryScript.lean');s=p.read_text();lines=s.splitlines();changes=[]
indent=lambda s:len(s)-len(s.lstrip())
def convert(lines):
 out=[];i=0
 while i<len(lines):
  line=lines[i];m=re.fullmatch(r'(\s*)match (\w+) with',line)
  if not m:out.append(line);i+=1;continue
  n=len(m[1]);cf=m[2];j=i+1;branches=[]
  for k in range(2):
   assert j<len(lines) and indent(lines[j])==n and lines[j].strip().startswith('|'),(cf,lines[j])
   pat=[]
   while '=>' not in lines[j]:pat.append(lines[j].strip());j+=1
   a,b=lines[j].strip().split('=>',1);pat.append(a);j+=1
   pattern=' '.join(pat).strip();pm=re.fullmatch(r'\| core\.ops\.control_flow\.ControlFlow\.(Continue|Break) (\w+|_)',pattern);assert pm,pattern
   block=[]
   if b.strip():block.append(' '*(n+2)+b.strip())
   while j<len(lines) and (not lines[j].strip() or indent(lines[j])>n):block.append(lines[j]);j+=1
   assert block,(cf,k)
   branches.append((pm[1],pm[2],convert(block)))
  assert [x[0] for x in branches]==['Continue','Break']
  out.append(' '*n+'control '+cf)
  for _,var,block in branches:
   out.append(' '*(n+2)+'(fun '+var+' => do')
   out += ['  '+x for x in block]
   out[-1]+=')'
  changes.append({'source_control_flow':cf,'rewrite':'total Continue/Break eliminator, both branches retained'})
  i=j
 return out
p.write_text('\n'.join(convert(lines))+'\n');(E/(p.stem+'_CONTROLS.json')).write_text(json.dumps(changes,indent=2)+'\n');print('Converted',len(changes),'complete ControlFlow eliminations')
