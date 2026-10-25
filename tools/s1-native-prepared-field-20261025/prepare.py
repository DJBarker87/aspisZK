#!/usr/bin/env python3
"""Real native field decoder inside original constructor/claim; canonical928-byte input domain."""
from pathlib import Path
import subprocess,sys,hashlib,json
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);T=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(R/'tools/s1-native-prepared-claim-20261025/prepare.py'),'--out',str(O),'--copied-inputs'],check=True)
f=O/'min/src/prepared_claim_native/proofs.rs';s=f.read_text()
field=subprocess.check_output(['git','show','25866ec331cc7ce27dd9956609c11d32fa8fa58a:crates/aspis-r1-cost-probe/src/weights.rs'],cwd=R,text=True).splitlines()[20]
assert field=='pub fn field(bytes:&[u8],i:usize)->E { E::from_le_bytes(&bytes[i*32..(i+1)*32]).unwrap() }'
original='assert!(index<29);assert!(CPUSH==145+index);CFIELD=index+1;FIELDS[index]'
replacement='assert!(index<29);assert!(CPUSH==145+index);CFIELD=index+1;let actual=native_field(bytes,index);same_e(actual,FIELDS[index]);actual'
assert s.count(original)==1;s=s.replace(original,replacement)
old='let y1=kani::any::<[u8;928]>();'
assert s.count(old)==1;s=s.replace(old,'let mut y1=[0u8;928];')
needle='let fail_at=if kani::any::<bool>(){0}else if stop<174{1}else{2};let error=any_error();'
assert s.count(needle)==1
s=s.replace(needle,needle+"\n let mut col=0;while col<29{let words=fields[col].to_limbs();let mut j=0;while j<8{let mut b=0;while b<4{y1[32*col+4*j+b]=(words[j]>>(8*b))as u8;b+=1;}j+=1;}col+=1;}\n")
a=s.index('let view=View{');b=s.index('};',a)+2
view=s[a:b];s=s[:a]+s[b:]
needle=' unsafe{SEM_CLAIMS='
assert s.count(needle)==1;s=s.replace(needle,' '+view+'\n'+needle)
s+='\n'+field.replace('pub fn field(','fn native_field(')+'\n'
f.write_text(s)
files={str(p.relative_to(O)):hashlib.sha256(p.read_bytes()).hexdigest() for p in O.rglob('*')if p.is_file()}
(O/'field-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=files,original_field=field,native_field=field.replace('pub fn field(','fn native_field('),primitive_cuts=8,domain='All29 records encode arbitrary canonical native E values; exact928bytes, not arbitrary malformed payloads. Full actual native field executes at each reached read, hook only observes index/pointer/order and equality; no arbitrary decoder return.',remaining='Actual caller canonical input connection must be consumed; eight normal-return cuts, native allocation/init/SDK/runtime/extraction/oracle/release remain open. Historical25866 component, not whole4bb3.',compiler_launched=False),indent=2)+'\n')
(T/'proofs.rs').write_text(s)
print(json.dumps(dict(status='SOURCE_ONLY',source_files=len(files),normal_return_cuts=8)))
