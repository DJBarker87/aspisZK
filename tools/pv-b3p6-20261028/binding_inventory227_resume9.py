"""Inventory all source/reference function bodies; no semantic credit from a diff.
String and comment tokens are retained in comparisons where semantically relevant.
"""
from pathlib import Path
import re,json,hashlib,difflib,sys
D=Path('evidence/pv-b3p6-20261028');O=D/'resume9';O.mkdir(exist_ok=True)
P=Path('tools/pv-b3p6-20261028/v244')
lex=re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|r\#*"[\s\S]*?"\#*|"(?:\\.|[^"\\])*"|\w+|[^\s]')
def tokens(s):return [(m[0],m.start(),m.end()) for m in lex.finditer(s) if not m[0].startswith(('//','/*'))]
def functions(path):
 s=path.read_text();ts=tokens(s);rows={};counts={}
 for i,(v,a,b) in enumerate(ts):
  if v!='fn':continue
  name=ts[i+1][0];j=i+2
  while ts[j][0]!='{':j+=1
  k=j+1;depth=1
  while depth:
   depth+=(ts[k][0]=='{')-(ts[k][0]=='}');k+=1
  ordinal=counts.get(name,0);counts[name]=ordinal+1;key=f'{name}#{ordinal}'
  rows[key]=dict(name=name,key=key,line=s[:a].count('\n')+1,end_line=s[:ts[k-1][2]].count('\n')+1,tokens=[x[0]for x in ts[i:k]],sha256=hashlib.sha256(s[a:ts[k-1][2]].encode()).hexdigest())
 return rows
pairs=[('terminal',P/'host_terminal.rs',P/'reference_terminal.rs'),('copy',P/'host_copy_terminal.rs',P/'reference_copy_terminal.rs'),('field',P/'host_terminal_field.rs',P/'reference_field.rs'),('poseidon',Path('crates/aspis-statement/src/state_only_poseidon.rs'),P/'reference_poseidon.rs')]
rows=[];files=[]
for family,a,b in pairs:
 src=functions(a);ref=functions(b)
 files.append(dict(family=family,source=str(a),owned=str(b),source_sha256=hashlib.sha256(a.read_bytes()).hexdigest(),owned_sha256=hashlib.sha256(b.read_bytes()).hexdigest()))
 for key in sorted(src.keys()|ref.keys()):
  x=src.get(key);y=ref.get(key)
  status='identical' if x and y and x['tokens']==y['tokens'] else 'changed' if x and y else 'source-only' if x else 'owned-only'
  row=dict(family=family,key=key,status=status,source=x,owned=y,source_binding='pending' if status!='identical' else 'token identity; reachability/configuration still checked separately')
  if x and y and status=='changed':row['token_changes']=[dict(tag=t,source=x['tokens'][i:j],owned=y['tokens'][k:l])for t,i,j,k,l in difflib.SequenceMatcher(None,x['tokens'],y['tokens'],autojunk=False).get_opcodes()if t!='equal']
  rows.append(row)
record=dict(classification='inventory only; not a body binding or native equality theorem',semantic_use='reclassification within existing Charon/Aeneas tool trust',own_1='deployed SOURCE statement-by-statement binding; compiler preservation V370 / pending D381,D386 retained; machine-code correspondence not required',feature_authority='native227-composition-features.json; cfg reachability must be applied before closure',files=files,bodies=rows,summary={k:sum(r['status']==k for r in rows)for k in ['identical','changed','source-only','owned-only']})
p=O/'body-inventory.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record['summary']))
