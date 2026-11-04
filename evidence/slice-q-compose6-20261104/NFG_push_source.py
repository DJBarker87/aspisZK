"""Exact original private/public push source cuts and range publication."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
ROOTS={
 'crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push':(6282,6644,'0690762c9d2c31673fed24b3cd4a34a41cd6383c4f53ff64079550dd817e420c'),
 'crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push':(7845,8134,'0a69f40fecb6fa1a3e661c695929992da16636379f1534e0ccb14bafe8f10395')}
def normalized(s):return re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
PRIVATE='''{let raw=a.raw(b);for j in 0..4 {self.sums[j]=self.sums[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31u32));}}'''
PUBLIC='''{if self.count >= MAX_TERMS { return Err(()); }let [value_c0,value_c1] = canonical::Q::from_wide(value);let scalar = checked_q(scalar)?;self.c0.push(value_c0, scalar);self.c1.push(value_c1, scalar);self.count += 1;Ok(())}'''
def check():
 source=subprocess.check_output(['git','show',REV+':crates/aspis-r1-cost-probe/src/fast_pairing.rs'],cwd=R)
 out=[]
 for root,(a,b,h) in ROOTS.items():
  body=source[a:b];assert hashlib.sha256(body).hexdigest()==h
  assert normalized(body.decode())==normalized(PRIVATE if '::canonical::' in root else PUBLIC)
  out.append(dict(root=root,range=[a,b],body_sha256=h))
 assert 'const MAX_TERMS: usize = 4096;' in source.decode()
 return dict(roots=out,private_order='one raw call, four successive SAME receiver states at 0,1,2,3; bound-4 endpoint',public_order='count rejection; conversion; scalar rejection; SAME c0 then c1 receiver; count publication',native_groups=['NFF_K019/020','NFF_K021/022','NFF_K068/069','NFF_K029/026'],range_group='NFG_K026/027 (scalar Range only)',root_math=['NFG_PushRoot.private','NFG_PushRoot.public','NFG_PushRoot.reject_count','NFG_PushRoot.reject_scalar'])
if __name__=='__main__':print(json.dumps(check(),indent=2))
