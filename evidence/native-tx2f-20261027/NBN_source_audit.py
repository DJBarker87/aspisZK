from pathlib import Path
import subprocess,json,hashlib,time
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2f-20261027'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'--','crates','programs'],text=True).splitlines();pins={p:hashlib.sha256(subprocess.check_output(['git','show',rev+':'+p])).hexdigest() for p in paths}
special={'crates/aspis-statement/src/lib.rs':('prefix','#![cfg_attr(kani, feature(next_index))]\n'),'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs':('suffix','\n#[cfg(kani)]\n#[path="NBN_more.rs"]\nmod NBN_more;\n')}
# Actual pair_terminal overlay retained in the committed decode patch; check exactly.
p='crates/aspis-statement/src/pool_v1/pair_terminal.rs'
patch=(E/'NBN_decode_fixed.patch').read_text();addition=''.join(l[1:]+'\n' for l in patch.splitlines() if l.startswith('+') and not l.startswith('+++'))
# The patch also contains the added module source. Only source-prefix additions
# are extracted from the first file's diff below, before the new file diff.
section=patch.split('--- /dev/null')[0]
addition=''.join(l[1:]+'\n' for l in section.splitlines() if l.startswith('+') and not l.startswith('+++'))
special[p]=('suffix',addition)
script=f'''from pathlib import Path
import hashlib,json
b=Path({B!r})/'NBN_src';pins={pins!r};special={special!r};out={{}}
for name,want in pins.items():
 p=b/name;raw=p.read_bytes();base=raw
 if name in special:
  side,extra=special[name];suffix=extra.encode()
  if side=='prefix':assert raw.startswith(suffix),name;base=raw[len(suffix):]
  else:assert raw.endswith(suffix),name;base=raw[:-len(suffix)]
 got=hashlib.sha256(base).hexdigest();assert got==want,(name,got,want)
 out[name]=dict(frozen_prefix_sha256=got,scratch_sha256=hashlib.sha256(raw).hexdigest(),cfg_kani_only=name in special)
print(json.dumps(dict(frozen_revision={rev!r},files=out,lock_sha256=hashlib.sha256((b/'Cargo.lock').read_bytes()).hexdigest())))
'''
for n in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3','-'],input=script,capture_output=True,text=True)
 if r.returncode!=255:break
 if n<10:time.sleep(60)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NBN_SOURCE_AUDIT.json').write_text(json.dumps(x,indent=2)+'\n');print(len(x['files']),'frozen native source files verified')
