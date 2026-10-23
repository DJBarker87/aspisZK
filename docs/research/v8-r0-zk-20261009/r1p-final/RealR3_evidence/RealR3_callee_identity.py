from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[5];E=R/'docs/research/v8-r0-zk-20261009/r1p-final/RealR3_evidence';P=R/'docs/research/100bit-spend-path-20261013/evidence/prover-commit30-20261022'
def item(s,n):
 a=s.index(n);i=s.index('{',a)+1;d=1
 while d:
  if s[i]=='{':d+=1
  elif s[i]=='}':d-=1
  i+=1
 return s[a:i]
w=(R/'crates/aspis-r1-cost-probe/src/r1_wire.rs').read_text();old=(P/'rust-sources/caller-v4-r1_wire.rs.txt').read_text()
ns=['pub const fn row_shape','fn validate_record_fields','pub fn parse_record','pub fn record','fn sample_block_validated','fn sample_block(','pub fn semantic(&mut self','pub mod fields20','pub mod semantic20']
out={}
for n in ns:
 x=item(w,n);y=item(old,n);assert x==y,n;out[n]=hashlib.sha256(x.encode()).hexdigest()
shared={}
for path in ['crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-core/src/digest.rs']:
 current=(R/path).read_bytes();before=subprocess.check_output(['git','show','e78e2c022fddebb3d379963ea09efbca478664a7:'+path],cwd=R)
 assert current==before,path
 shared[path]=hashlib.sha256(current).hexdigest()
receipts={}
for name in ['semantic30-summary-all-rows-v1','semantic30-all-rows-modular-v1','fields30-one-cell-v2','fields30-exact896-v1','fields30-owned896-v1','fields30-owned32-v1']:
 d=P/'receipts'/name;rec=json.loads((d/'receipt.json').read_text())
 assert rec['exit_status']==0
 assert 'VERIFICATION:- SUCCESSFUL' in (d/'stdout.log').read_text()
 receipts[name]={'path':str(d.relative_to(R)), 'exit':rec['exit_status'], 'hashes':{f:hashlib.sha256((d/f).read_bytes()).hexdigest() for f in ['receipt.json','stdout.log','stderr.log','time.log']}}
(E/'RealR3_callee30-identity.json').write_text(json.dumps({'historical_source':str(P.relative_to(R))+'/rust-sources/caller-v4-r1_wire.rs.txt','identity':out,'part30_shared_file_identity':shared,'receipt_integrity':receipts,'reused_receipts':['semantic30-summary-all-rows-v1','semantic30-all-rows-modular-v1','fields30-one-cell-v2','fields30-exact896-v1','fields30-owned896-v1','fields30-owned32-v1'],'scope':'rows <25; record <=901; exact errors/state/counter, validation congruence and ordered three-read history; common pure sampler; successful allocations'},indent=2)+'\n')
