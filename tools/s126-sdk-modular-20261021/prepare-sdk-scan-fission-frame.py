#!/usr/bin/env python3
"""Check actual scan-fission probe footprints on the original native SDK path.
Source probe bodies are unchanged from constructor-ready-v4. The enter probe
is verified at its real source call site with an empty write set. The leave
probe has a separate all-bool ghost-only contract. No SDK/guard model is used.
These checks do not themselves establish the whole SDK caller join.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);mode=sys.argv[2];assert mode in ['enter','leave'] and not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-constructor-ready.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();old=s
if mode=='enter':
 needle='pub fn scan_enter(';assert s.count(needle)==1;s=s.replace(needle,'#[kani::modifies()]\n'+needle)
 needle='#[kani::proof] #[kani::unwind(48)]';assert s.count(needle)==1;s=s.replace(needle,'#[kani::proof_for_contract(scan_enter)] #[kani::unwind(48)]')
else:
 needle='pub fn scan_leave(';assert s.count(needle)==1;s=s.replace(needle,'''#[kani::modifies(unsafe{std::ptr::addr_of_mut!(SCAN_RESULT.value)})]
#[kani::ensures(|_|unsafe{SCAN_RESULT.value}==Some(hit))]
'''+needle)
 end=s.rfind('\n}');assert end>0;s=s[:end]+'''
#[kani::proof_for_contract(scan_leave)] #[kani::unwind(4)]
fn scan_leave_contract(){
 let hit:bool=kani::any();let initial:Option<bool>=kani::any();
 unsafe{SCAN_RESULT.value=initial;}
 scan_leave(hit);
 kani::cover!(hit,"scan_leave records true");
 kani::cover!(!hit,"scan_leave records false");
}
'''+s[end:]
# A body-preserving proof instrumentation only.
def body(src,name):
 a=src.index('pub fn '+name+'(');b=src.index('{',a)+1;d=1
 while d:d+=(src[b]=='{')-(src[b]=='}');b+=1
 return src[a:b]
for name in ['scan_enter','scan_leave']:assert body(old,name)==body(s,name)
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('constructor-ready-v4','scan-fission-'+mode+'-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,mode=mode,probe_body_unchanged=True,expected_time=('Cached optimized compilation then actual source-site scan_enter empty footprint, std-any read-only overapproximation; one180s capped check.' if mode=='enter' else 'Cached optimized compilation then all-bool ghost-only scan_leave frame/value check.'),remaining='All properties and covers must pass. Together with the checked constructor-site assertions and exact source let/iterator/any order, establish ghost erasure; full native SDK/caller/child/runtime/oracle/TX2 composition remains.'),indent=2)+'\n')
