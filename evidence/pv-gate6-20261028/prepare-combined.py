from pathlib import Path
import subprocess,json,hashlib
P=Path('tools/pv-integ4-20261027');E=Path(__file__).resolve().parent
D='/home/dombarker/project-offloads/codex-pv-gate6-20261028';OLD='/home/dombarker/project-offloads/codex-pv-integ4-20261027';HOST='dombarker@100.108.41.90'
REV='82566acdfb488183022f41ac564c11df22c9404f';CONTROL='c57a344726745387efb38d1571d885c69ce829ee'
def remote(code):
 r=subprocess.run(['ssh',HOST,'python3','-'],input=code,text=True,capture_output=True);r.check_returncode();return r.stdout
# Called only after A1 and a successful recorded admission.
remote(f'''from pathlib import Path
D=Path({D!r});(D/'combined/baseline/source').mkdir(parents=True);(D/'combined/candidate').mkdir()
(D/'combined/candidate/source').symlink_to(D/'source',target_is_directory=True)
(D/'combined/candidate/native-target').symlink_to(D/'native-target',target_is_directory=True)
''')
a=subprocess.Popen(['git','archive',CONTROL,'Cargo.toml','Cargo.lock','.cargo','crates','programs','audit','xtask','tools','docs/research/v8-r0-zk-20261009/refine','docs/research/v8-r0-zk-20261009/c3','docs/research/v8-r0-zk-20261009/z4'],stdout=subprocess.PIPE)
r=subprocess.run(['ssh',HOST,f'tar xf - -C {D}/combined/baseline/source'],stdin=a.stdout);a.stdout.close();assert r.returncode==0 and a.wait()==0
payload={}
for who,rev in [('baseline',CONTROL),('candidate',REV)]:
 for name in ['native.py','capped.py','capped-template.py','reservation.py']:
  payload[who+'/'+name]=(P/name).read_text().replace(OLD,D+'/combined/'+who)
 payload[who+'/source-revision.txt']=rev+'\n'
for name in ['run_host.py','capped.py','capped-template.py']:
 payload[name]=(P/name).read_text().replace(OLD,D+'/combined')
payload['corpus.py']=(P/'combined-corpus.py').read_text().replace(OLD,D)
payload['audit-corpus.py']=(P/'audit-corpus.py').read_text().replace(OLD,D)
payload['source-revision.txt']=REV+'\n'
remote(f'''from pathlib import Path
import json,hashlib
D=Path({(D+'/combined')!r});payload={payload!r}
for n,s in payload.items():(D/n).write_text(s)
(D/'runner-pins.json').write_text(json.dumps({{n:hashlib.sha256(s.encode()).hexdigest() for n,s in payload.items()}},indent=2))
''')
rows=json.loads(remote(f'''from pathlib import Path
import hashlib,json
D=Path({(D+'/combined/baseline/source')!r});print(json.dumps({{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file()}}))
'''))
p=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE);bad=[]
for path,h in rows.items():
 p.stdin.write((CONTROL+':'+path+'\n').encode());p.stdin.flush();head=p.stdout.readline().split();assert head[1]==b'blob';data=p.stdout.read(int(head[2]));assert p.stdout.read(1)==b'\n'
 if hashlib.sha256(data).hexdigest()!=h:bad.append(path)
p.stdin.close();p.wait();assert not bad
(E/'control-source-identity.json').write_text(json.dumps(dict(revision=CONTROL,files=rows,disagreements=bad,passed=not bad),indent=2)+'\n')
