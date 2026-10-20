#!/usr/bin/env python3
"""Generate a dependency-free, body-exact scanner cut; no shipped file changes."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[2]
out=Path(sys.argv[1]); out.mkdir(parents=True,exist_ok=True)
src=root/'crates/aspis-core/src/r0_transcript.rs'
s=src.read_text()
def item(marker):
 start=s.index(marker); b=s.index('{',start); depth=1; end=b+1
 while depth:
  depth += (s[end]=='{')-(s[end]=='}'); end+=1
 return s[start:end]
parts=['type Rank = [u32; 8];','pub const QUERY_COUNT: usize = 22;','pub const QUERY_BOUND: u32 = 1 << 18;','pub const QUERY_MAX_DRAWS: usize = 64;',item('fn block_rank('),item('fn query_words('),'#[derive(Default)]\n'+item('struct QueryScan {'),item('impl QueryScan {'),item('pub fn queries_from_pairs(')]
trans=(root/'crates/aspis-core/src/transcript.rs').read_text()
start=trans.index('pub enum QuerySampleError {'); end=trans.index('\n}',start)+2
parts.insert(0,'#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+trans[start:end])
body='\n\n'.join(parts)+'\n'
harness=(root/'tools/r4-transport-kit/harness.rs').read_text()
start=harness.index('fn scan_contract('); b=harness.index('{',start);depth=1;end=b+1
while depth:
 depth += (harness[end]=='{')-(harness[end]=='}');end+=1
expected=item('fn scan(').replace('fn scan(', 'fn scan_contract(').replace('self.accepted[..self.accepted_len].contains(&candidate)', 'prefix_contract(&self.accepted,self.accepted_len,candidate)')
assert ''.join(expected.split()) == ''.join(harness[start:end].split()), 'Contract scanner differs outside the one verified membership substitution'

(out/'src').mkdir(exist_ok=True)
(out/'src/lib.rs').write_text(body+'\n'+(root/'tools/r4-transport-kit/harness.rs').read_text())
(out/'Cargo.toml').write_text('[package]\nname="r4-transport-scanner"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
(out/'source-cut.json').write_text(json.dumps({'source':str(src.relative_to(root)),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'cut_sha256':hashlib.sha256(body.encode()).hexdigest(),'items':parts,'membership_substitution':{'from':'self.accepted[..self.accepted_len].contains(&candidate)','to':'prefix_contract(&self.accepted,self.accepted_len,candidate)','check':'Complete scan body matches after only this substitution; Kani contracts cover each prefix length0..22'},'qualification':'Exact complete scanner bodies plus Rank/constants/error data. No field/circle/hash stubs; no transcript implementation included. Harness uses Kani Rust standard library directly.'},indent=2)+'\n')
