from pathlib import Path
import subprocess,json,hashlib,tarfile,io
w=Path.cwd();rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();pins=json.loads((w/'.j1-r17/terminal-decoder/range-source-pins.json').read_text());pins['source_revision']=rev
refs=[rev+':'+n for n in pins['kit_files']];raw=subprocess.run(['git','cat-file','--batch'],input=('\n'.join(refs)+'\n').encode(),stdout=subprocess.PIPE,check=True).stdout;stream=io.BytesIO(raw);files={}
for rel in pins['kit_files']:
 h=stream.readline().split();assert h[1]==b'blob';data=stream.read(int(h[2]));assert stream.read(1)==b'\n';pins['kit_files'][rel]=hashlib.sha256(data).hexdigest()
 if rel in ['crates/aspis-statement/src/atomic_statement.rs','crates/aspis-statement/src/pool_v1/pair_tree_profile.rs','crates/aspis-statement/src/pool_v1/payment_relation.rs']:files[rel]=data
assert not stream.read();files['source-pins.json']=(json.dumps(pins,indent=2)+'\n').encode();out=w/'.j1-r17/terminal-decoder/copy-helper-additions.tar.gz'
with tarfile.open(out,'w:gz') as t:
 for n,d in files.items():i=tarfile.TarInfo(n);i.size=len(d);i.mode=0o644;t.addfile(i,io.BytesIO(d))
subprocess.run(['scp',str(out),'dombarker@100.108.41.90:/home/dombarker/project-offloads/aspis-r1-j1a-terminal-decoder-20261016/copy-helper-additions.tar.gz'],check=True)
print(rev,len(pins['kit_files']))
