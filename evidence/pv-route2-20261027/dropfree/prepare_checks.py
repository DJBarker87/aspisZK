from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
vectors=[]
for n in [0,1,2,55,56,57,63,64,65,119,120,127,128,129,255,1024]:
 b=bytes((i*73+19)%256 for i in range(n));vectors.append((b,hashlib.sha256(b).digest()))
s='\n#[cfg(test)] mod checks {use super::*;\n#[test] fn sha256_boundaries_and_chunking(){\n'
for b,out in vectors:
 s+='let input=['+','.join(map(str,b))+'];let expected=['+','.join(map(str,out))+'];let mut whole=new();update(&mut whole,&input);assert_eq!(finalize(whole),expected);let mut split=new();let mut i=0;while i<input.len(){update(&mut split,&input[i..i+1]);i+=1;}assert_eq!(finalize(split),expected);\n'
s+='}}\n';(D/'digest_checks.rs').write_text(s)
# Endpoint masks match shipped sorted active row fingerprint before extraction.
s=(D/'probes/134.rs').read_text();import re,collections
pairs=[tuple(map(int,x)) for x in re.findall(r'\((\d+),(\d+)\)',s)];rows=sorted(set(a for a,b in pairs)|set(b for a,b in pairs));h=0xcbf29ce484222325
for row in rows:
 for byte in row.to_bytes(2,'little'):h=((h^byte)*0x100000001b3)&((1<<64)-1)
assert h==0xdf394a5a8554d09c
(D/'forest-precheck.json').write_text(json.dumps(dict(links=len(pairs),active_rows=len(rows),active_rows_fingerprint=hex(h),shipped_fingerprint='0xdf394a5a8554d09c',kind='finite source-data check; no source-equivalence theorem'),indent=2)+'\n')
