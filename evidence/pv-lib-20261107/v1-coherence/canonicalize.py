"""Redirect imports of byte-identical mirror bodies to their canonical modules.
Declaration bodies and all theorem statements are preserved byte-for-byte.
"""
import pathlib,json,re,hashlib,subprocess
E=pathlib.Path(__file__).parent;x=json.loads((E/'IMPORT_CANONICALIZATION.json').read_text());aliases=x['aliases'];changes={}
strip=lambda s:'\n'.join(l for l in s.splitlines() if not l.startswith('import '))
for p in pathlib.Path('lean').glob('*.lean'):
 old=p.read_text();new=re.sub(r'(?m)^import (\S+)',lambda m:'import '+aliases.get(m[1],m[1]),old)
 if new==old:continue
 assert strip(old)==strip(new),p
 p.write_text(new);changes[p.stem]=dict(path=str(p),before_sha256=hashlib.sha256(old.encode()).hexdigest(),after_sha256=hashlib.sha256(new.encode()).hexdigest(),before_imports=re.findall(r'^import (\S+)',old,re.M),after_imports=re.findall(r'^import (\S+)',new,re.M),declarations_unchanged=True)
x['changes']=changes;(E/'IMPORT_CANONICALIZATION.json').write_text(json.dumps(x,indent=2)+'\n');print('import-only repairs',len(changes))
