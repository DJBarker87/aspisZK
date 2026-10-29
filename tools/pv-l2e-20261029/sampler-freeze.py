"""Freeze byte-identical native helper bodies; value comparison, not trace proof."""
from pathlib import Path
import json,hashlib,subprocess
E=Path('evidence/pv-l2e-20261029');out=[];records=[]
def body(p,name):
 s=Path(p).read_text();start=s.index('fn '+name+'(');a=s.index('{',start);depth=1;i=a+1
 while depth:
  depth += (s[i]=='{')-(s[i]=='}');i+=1
 t=s[start:i];records.append(dict(path=p,name=name,file_sha256=hashlib.sha256(s.encode()).hexdigest(),body_sha256=hashlib.sha256(t.encode()).hexdigest(),original=t,cfg='no feature or debug cfg in reachable release helper except debug_assert; release disables debug assertions'))
 return t
out.append('const P:u32=2147483647;')
for p,name in [('crates/aspis-r1-cost-probe/src/sampler.rs','qm31_div_pass'),('crates/aspis-r1-cost-probe/src/sampler.rs','qm31_digits'),('crates/aspis-r1-cost-probe/src/host_sampler.rs','low_base_p_digits'),('crates/aspis-r1-cost-probe/src/host_sampler.rs','add_small_base_p')]:out.append(body(p,name))
out.append('pub fn low(b:&[u8;32])->([u32;8],u32){low_base_p_digits(b)}\npub fn qm(b:&[u8;32])->[u32;4]{qm31_digits(b)}\npub fn add(d:&mut[u32;8],a:u32)->bool{add_small_base_p(d,a)}')
(E/'sampler-raw.rs.txt').write_text('\n'.join(out)+'\n')
(E/'sampler-source-freeze.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),bodies=records,evidence_class='finite native validation; exact source helper bodies; not a universal full-trace or deployed-artifact law',replacements='none; four public wrappers only; P is the identical literal'),indent=2)+'\n')
print('Frozen four unedited helper bodies')
