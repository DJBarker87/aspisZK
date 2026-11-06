"""Generate reviewed fixed-SolanaDigest cuts from frozen bodies, no handwritten body."""
from pathlib import Path
import re,json,subprocess,hashlib
E=Path(__file__).resolve().parent
src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/transcript.rs'],text=True)
def method(n):
 m=re.search(r'pub fn '+n+r'\(',src);a=src.index('{',m.start());i=a+1;depth=1
 while depth:depth+=(src[i]=='{')-(src[i]=='}');i+=1
 return src[m.start():i]
methods=[];pins={}
for n in ['new','absorb','block']:
 raw=method(n)
 s=raw
 if n=='new':s=s.replace('hash:H,','hash:SolanaDigest,').replace('variant:Variant)','variant:Variant, log:&mut Log)')
 else:s=s.replace('payload:&[u8])','payload:&[u8], log:&mut Log)')
 s=s.replace('self.absorb(row,payload);','self.absorb(row,payload,log);')
 for old in ['hash.digest(&[domain,&[variant.tag()],&semantic_state])','self.hash.digest(&[&self.state,&[0,0xa0+row],&(payload.len() as u32).to_le_bytes(),payload])','self.hash.digest(&[&self.state,&[1]])','self.hash.digest(&[&self.state,&[2]])']:
  receiver,args=old.split('.digest(',1)
  s=s.replace(old,'observed_digest(&'+receiver+','+args[:-1]+',log)')
 assert '.digest(' not in s
 methods.append(s);pins[n]=dict(frozen_body_sha256=hashlib.sha256(raw.encode()).hexdigest(),reviewed_cut_sha256=hashlib.sha256(s.encode()).hexdigest(),frozen_body=raw,cut_body=s)
text=(E/'NKD_native.rs.txt').read_text().replace('NKD_METHODS','\n'.join(methods))
(E/'NKD_native_generated.rs.txt').write_text(text)
(E/'NKD_NATIVE_CORRESPONDENCE.json').write_text(json.dumps(pins,indent=1)+'\n')
print('Generated three source-ordered SolanaDigest cut bodies')
