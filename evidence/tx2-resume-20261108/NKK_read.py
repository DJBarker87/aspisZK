from pathlib import Path
import json,lzma,hashlib,sys
E=Path(__file__).resolve().parent
n=sys.argv[1];p=E/n
if p.exists():b=p.read_bytes()
elif (E/(n+'.xz')).exists():b=lzma.decompress((E/(n+'.xz')).read_bytes())
else:
 x=json.loads((E/'NKK_INPUT_INDEX.json').read_text())[n];b=lzma.decompress((E/x['capsule']).read_bytes());assert hashlib.sha256(b).hexdigest()==x['sha256'];assert len(b)==x['bytes']
sys.stdout.buffer.write(b)
