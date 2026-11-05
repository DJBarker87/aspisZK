from pathlib import Path
import re,json,hashlib
B=Path(__file__).resolve().parent;S=B/'NIX_src'
def body(s,needle):
 i=s.index(needle);i=s.index('{',i);start=i+1;depth=1
 while depth:
  i+=1;depth+=(s[i]=='{')-(s[i]=='}')
 return s[start:i]
def norm(s):return re.sub(r'\s+','',re.sub(r'//[^\n]*','',s))
report={}
source=(S/'crates/aspis-r1-cost-probe/src/sampler.rs').read_text().split('#[cfg(kani)]')[0]
raw=body(source,'pub fn circle_sample(')
expected=raw.replace('secure_ood_circle_point_from_parameter(qm31_sample(block))','map(sample(block,q,log),mapped,log)')
expected=expected.replace('aspis_core::transcript::circle_fallback_point(match row {','fallback(match row {').replace('        })','        },fb,log)')
cut=body((B/'NIX_sampler.rs.txt').read_text(),'fn step(')
assert norm(expected).replace(',}','}')==norm(cut).replace(',}','}'),('sampler body mismatch',expected,cut)
report['sampler']=dict(frozen_body_sha256=hashlib.sha256(raw.encode()).hexdigest(),cut_sha256=hashlib.sha256(cut.encode()).hexdigest(),token_erasure=True,callee_replacements=['qm31_sample','secure_ood_circle_point_from_parameter','circle_fallback_point'])
source=(S/'crates/aspis-r1-cost-probe/src/r1_wire.rs').read_text().split('#[cfg(kani)]')[0]
raw=body(source,'pub(crate) fn circle_validated(')
expected=raw.replace('circle_sample(','circle(').replace('self.sample_block_validated(row, record.framed())','block(t,row,record.framed(),reply,new_state,new_next,log)').replace('            circle_row,','            circle_row,point,log,')
cut=body((B/'NIX_validated.rs.txt').read_text(),'fn step<')
# Ignore the optional final comma, as in the Rust parser itself.
canon=lambda x:norm(x).replace(',)',')').replace(',}','}')
assert canon(expected)==canon(cut),('validated body mismatch',expected,cut)
report['validated']=dict(frozen_body_sha256=hashlib.sha256(raw.encode()).hexdigest(),cut_sha256=hashlib.sha256(cut.encode()).hexdigest(),token_erasure=True,callee_replacements=['sample_block_validated','circle_sample'],deployed_instantiation='programs/r1-cost-probe/src/lib.rs::SolanaDigest')
(B/'NIX_CALLER_ERASURE.json').write_text(json.dumps(report,indent=2));print('NIX caller token erasure checks passed')
