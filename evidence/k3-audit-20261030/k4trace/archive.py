from pathlib import Path
import lzma,hashlib,json
E=Path(__file__).resolve().parent;rows=[]
for p in sorted(E.rglob('*')):
 if not p.is_file() or p.suffix=='.xz' or p.stat().st_size<=1024*1024:continue
 raw=p.read_bytes();q=Path(str(p)+'.xz');q.write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'  '+p.name+'\n');p.unlink();rows.append(str(p.relative_to(E)))
def adjust(v):
 if isinstance(v,str)and v.startswith('host/')and not (E/v).exists()and (E/(v+'.xz')).exists():return v+'.xz'
 if isinstance(v,list):return [adjust(x)for x in v]
 if isinstance(v,dict):return {k:adjust(x)for k,x in v.items()}
 return v
for p in [*E.glob('C*.json'),*E.glob('K931*.json')]:p.write_text(json.dumps(adjust(json.loads(p.read_text())),indent=2)+'\n')
print('compressed',len(rows),'artifacts')
