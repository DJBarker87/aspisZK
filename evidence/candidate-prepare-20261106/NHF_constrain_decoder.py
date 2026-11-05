"""Constrain the local decoder log to its CLOSED full byte/Option packet law."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;p=E/'NHF_wide.rs.txt';s=p.read_text()
old='self.calls+=1;assert!(bytes.as_ptr() as usize==self.proof+7495&&bytes.len()==32);self.reply'
new='''self.calls+=1;assert!(bytes.as_ptr() as usize==self.proof+7495&&bytes.len()==32);
 let mut canonical=true;let mut i=0;
 while i<8{let at=4*i;let word=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);canonical=canonical&&word<2147483647;i+=1;}
 match self.reply{
  None=>kani::assume(!canonical),
  Some(value)=>{kani::assume(canonical);let limbs=value.to_limbs();let mut j=0;
   while j<8{let at=4*j;let word=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);kani::assume(limbs[j]==word);j+=1;}}
 }
 self.reply'''
assert old in s;s=s.replace(old,new).replace('let result=cut(&proof,&semantic,&y1,&mut log);','let result=cut(&proof,&semantic,&y1,&mut log);\n kani::cover!(reply.is_some());kani::cover!(reply.is_none());')
s=s.replace('// The overapproximation accepts every CLOSED decoder reply. Lean supplies its\n// full byte/Option law on the SAME logged input; no decoder success is assumed.','// Full byte/Option packet constraints are enforced in DecodeLog::decode.\n// The same-input natural law is NHF_ViewDecoder.result; no success premise.')
p.write_text(s)
pins=json.loads((E/'NHF_SOURCE_PINS.json').read_text());pins['crates/aspis-r1-cost-probe/src/NHF_wide.rs']=hashlib.sha256(p.read_bytes()).hexdigest();(E/'NHF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
# Rebuild the additions in the existing patch without changing its frozen hunks.
p=E/'NHF_native.patch';patch=p.read_text();start=patch.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NHF_wide.rs\n');patch=patch[:start]+''.join(__import__('difflib').unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NHF_wide.rs'));p.write_text(patch)
