"""Host-only copy, hash and verify existing NFY cache; never mutate its source."""
from pathlib import Path
import shutil,hashlib,json,lzma,subprocess,os
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-s-retarget3-20261104';C=P/'codex-cx-slice-s-retarget3-cache-20261104';S=P/'codex-cx-slice-s-retarget-cache-20261104';W=P/'codex-cx-sound-int2-20261025'
B.mkdir(exist_ok=True);C.mkdir(exist_ok=True)
# Reservation is logged before any transfer or prover launch.
with (B/'NGF_SEED_RESERVATION.log').open('w') as f:r=subprocess.run(['python3',str(P/'codex-cx-s2h-20261023/S2H_reservation.py'),str(B/'NGF_SEED_RESERVATION.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((B/'NGF_SEED_RESERVATION.json').read_text());assert r.returncode==0 and a.get('allowed') is True,('wait-and-retry',r.returncode,a)
pins=[]
for p in sorted(S.rglob('*')):
 if not p.is_file():continue
 rel=p.relative_to(S);dest=C/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 if not dest.exists():shutil.copy2(p,dest)
 h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(dest.read_bytes()).hexdigest()==h
 pins.append(dict(source=str(p),destination=str(dest),sha256=h,bytes=dest.stat().st_size))
# A plain copy breaks predecessor hardlinks. Re-link only equal, verified
# files INSIDE the owned cache; every pathname and object byte is retained.
seen={};unique_bytes=0
for pin in pins:
 dest=Path(pin['destination']);key=(pin['sha256'],pin['bytes'])
 if key in seen:
  prior=seen[key]
  if dest.stat().st_ino!=prior.stat().st_ino:
   temp=dest.with_name(dest.name+'.NGF_dedup_tmp');os.link(prior,temp);os.replace(temp,dest)
 else:seen[key]=dest;unique_bytes+=pin['bytes']
assert unique_bytes<20*1024**3

raw=json.dumps(dict(source=str(S),selected=pins,bytes=sum(p['bytes'] for p in pins),unique_bytes=unique_bytes,seed_correction='Initial plain copy occupied 29G; content-preserving owned-only hardlink deduplication retains every path and byte.'),sort_keys=True).encode()
(B/'NGF_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NGF_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(W/n,B/n)
for n in ['NGF_objects','NGF_native','NGF_tmp']:(B/n).mkdir(exist_ok=True)
print(json.dumps(dict(files=len(pins),bytes=sum(p['bytes'] for p in pins),sha256=hashlib.sha256(raw).hexdigest())))
