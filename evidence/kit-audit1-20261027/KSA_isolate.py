from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
files=sorted(Path('evidence/extraction-assoc6-20261027').glob('XRn_Join_*.lean'))
mapping={p.stem:'KSA_'+p.stem for p in files}
rows=[]
for p in files:
 original=p.read_text();s=original
 for old,new in mapping.items():s=re.sub(r'(?m)^import '+re.escape(old)+r'$', 'import '+new,s)
 s=s.replace('_root_.XRn_Join_Release.','_root_.KSA_Isolated.XRn_Join_Release.').replace('_root_.compact.','_root_.KSA_Isolated.compact.')
 # Namespace scope changes declarations' names only. Import header stays at top level.
 pos=max(m.end() for m in re.finditer(r'(?m)^import [^\n]+\n',s))
 closing=('\nend\n' if p.stem=='XRn_Join_Funs' else '')+'\nend KSA_Isolated\n'
 s=s[:pos]+'\nnamespace KSA_Isolated\n'+s[pos:]+closing
 q=E/(mapping[p.stem]+'.lean');q.write_text(s)
 inverse=s.replace('\nnamespace KSA_Isolated\n','',1).removesuffix(closing)
 inverse=inverse.replace('_root_.KSA_Isolated.XRn_Join_Release.','_root_.XRn_Join_Release.').replace('_root_.KSA_Isolated.compact.','_root_.compact.')
 for old,new in mapping.items():inverse=re.sub(r'(?m)^import '+re.escape(new)+r'$', 'import '+old,inverse)
 assert inverse==original,p
 rows.append(dict(source=str(p),copy=str(q),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),copy_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),reverse_name_only_byte_identical=True))
(E/'KSA_isolation.json').write_text(json.dumps(rows,indent=2)+'\n')
# Topological ordering of only the private copies; all other imports are retained objects.
order=[]
def visit(n):
 if n in order:return
 p=E/(n+'.lean')
 for d in re.findall(r'^import (\S+)',p.read_text(),re.M):
  if d in mapping.values():visit(d)
 order.append(n)
visit('KSA_XRn_Join_Funs')
(E/'KSA_isolation_order.json').write_text(json.dumps(order,indent=2)+'\n')
print(len(order),'private copies')
