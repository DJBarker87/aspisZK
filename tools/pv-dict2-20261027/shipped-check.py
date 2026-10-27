from pathlib import Path
import subprocess,json,hashlib,re
E=Path('evidence/pv-dict2-20261027');rows=[]
for p in subprocess.check_output(['git','diff','73070ddd51','HEAD','--name-only','--','crates/','programs/'],text=True).splitlines():
 old=subprocess.check_output(['git','show','73070ddd51:'+p]);new=Path(p).read_bytes();assert new.startswith(old),p;s=new[len(old):].decode();mods=[]
 cleaned=re.sub(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])\'',lambda m:' ' * len(m[0]),s,flags=re.S);pos=0
 while cleaned[pos:].strip():
  m=re.match(r'\s*#\[cfg\(kani\)\]\s*(?:pub\(crate\)\s+)?mod\s+(\w+)\s*\{',cleaned[pos:]);assert m,(p,cleaned[pos:pos+100]);mods.append(m[1]);pos+=m.end();depth=1
  while depth:
   depth+=(cleaned[pos]=='{')-(cleaned[pos]=='}');pos+=1
 rows.append(dict(path=p,base_bytes=len(old),base_sha256=hashlib.sha256(old).hexdigest(),integrated_sha256=hashlib.sha256(new).hexdigest(),appended_bytes=len(s.encode()),cfg_kani_modules=mods,production_prefix_byte_equal=True))
assert len(rows)==3
(E/'shipped-additions.json').write_text(json.dumps(rows,indent=2)+'\n');print([(r['path'],len(r['cfg_kani_modules'])) for r in rows])
