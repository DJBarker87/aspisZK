from NBW_host import *
import sys,hashlib,fcntl
_serial=(E/'NBW_SERIAL.lock').open('a');fcntl.flock(_serial,fcntl.LOCK_EX)
admit(sys.argv[1])
s=(E/'NBW_native.rs.txt').read_text()
code=f'''from pathlib import Path
import hashlib,json
b=Path({B!r});p=b/'NBW_src/crates/aspis-r1-cost-probe/src'
(p/'NBW_native.rs').write_text({s!r})
f=p/'lib.rs';s=f.read_text();marker='#![cfg_attr(kani, recursion_limit = "512")]\\n'
if marker not in s:f.write_text(marker+s)
print(json.dumps(dict(source=hashlib.sha256((p/'NBW_native.rs').read_bytes()).hexdigest(),lib=hashlib.sha256(f.read_bytes()).hexdigest())))
'''
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3 -'],input=code,capture_output=True,text=True)
 if r.returncode!=255:break
 if trial<10:time.sleep(60)
assert r.returncode==0,r.stderr
(E/(sys.argv[1]+'-source.json')).write_text(r.stdout)
