from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent;H='/home/dombarker/project-offloads/';J=H+'codex-pv-k4trace-20261104';S='c535295ce34';T='2db53bdeb0d396e4bf3263a0d0fdd516c4c0b8a8';R='100d9075d2f'
def get(r,p):return subprocess.check_output(['git','show',r+':'+p])
payload={};provenance={}
def add(dst,r,p,want=None):
 b=get(r,p);h=hashlib.sha256(b).hexdigest();assert want is None or h==want,(dst,h,want)
 payload[dst]=b.decode();provenance[dst]={'revision':r,'path':p,'sha256':h}
# Restore old C084 bytes privately; absolute KMX path remains verbatim and is hash-checked.
cp=json.loads((E/'source-config.json').read_text())['C084']['pins']
for p in ['cblib/lib.rs','KMX_stubs.rs']:add('kstub/'+p,R,'evidence/pv-kstub-20261028/K12/'+Path(p).name+'.txt',cp[p])
for p in ['cblib/Cargo.toml','cblib/Cargo.lock']:
 # Source manifest bytes are recovered from the original committed k3 input bundle.
 pass
# The original manifest and lock are unchanged on host; payload collector records them below.
rows=[]
for cred,pos,neg in [('C044','K79200','K79201'),('C088','K79220','K79221'),('C089','K79222','K79223')]:
 for n in [pos,neg]:
  rec=json.loads((E/f'original/{n}/receipt.json').read_text());cmd=rec['command'];rows.append({'credit':cred,'original':n,'command':cmd,'cwd':str(Path(cmd[cmd.index('--manifest-path')+1]).parent),'negative':n==neg,'timeout':900,'root':json.loads((E/'source-config.json').read_text())[cred]['root'],'pins':json.loads((E/f'original/{n}/source-sha256.json').read_text())})
# C084 is placed immediately after C044.
krows=[]
for n,h in [('K12','split_checks::string_path'),('K13','split_checks::string_path_negative')]:
 rec=json.loads((E/f'original/{n}/receipt.json').read_text());cmd=rec['target'];cmd=cmd[cmd.index('cargo'):];cmd[cmd.index('--manifest-path')+1]=J+'/sources/kstub/cblib/Cargo.toml'
 krows.append({'credit':'C084','original':n,'command':cmd,'cwd':J+'/sources/kstub/cblib','negative':n=='K13','timeout':900,'root':J+'/sources/kstub','pins':cp})
rows[2:2]=krows
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',T,'tools/pv-stx-20261104/clone-certificate','tools/pv-stx-20261104/kmx','crates/aspis-core']).decode().splitlines()
for p in paths:add('stx/'+p,T,p)
for n in ['K93109','K93110','K93111']:
 d=json.loads((E/f'original/{n}/command.json').read_text());cmd=d['command'];cmd=cmd[cmd.index('cargo'):];cmd[cmd.index('--manifest-path')+1]=J+'/sources/stx/tools/pv-stx-20261104/clone-certificate/Cargo.toml'
 rows.append({'credit':n,'original':n,'command':cmd,'cwd':J+'/sources/stx','negative':'included','timeout':540,'root':J+'/sources/stx','pins':{p[len('stx/'):]:d['sha256'] for p,d in provenance.items() if p.startswith('stx/')}})
for i,r in enumerate(rows):r['id']='K'+str(93500+i)
(E/'source-payload.json.xz').write_bytes(lzma.compress(json.dumps(payload).encode()))
(E/'source-provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
(E/'runs.json').write_text(json.dumps(rows,indent=2)+'\n')
print([(r['id'],r['credit'],r['original']) for r in rows])
