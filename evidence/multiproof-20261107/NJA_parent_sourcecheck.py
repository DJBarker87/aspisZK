from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
raw=subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/multiproof.rs'],text=True);program=subprocess.check_output(['git','show',rev+':programs/r1-cost-probe/src/lib.rs'],text=True);log=(E/'NJA_parent.rs').read_text()
def body(s,name):
 m=re.search(r'fn '+name+r'(?:<[^\n]*>)?\s*\(',s);assert m,name
 i=s.index('{',m.end());j=i+1;n=1
 while n:n+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1]
def norm(x):return re.sub(r'\s+','',x)
checks={}
for source,cut in [('occupied_binary_parent','NJA_occupied'),('sibling_binary_parent','NJA_sibling')]:
 a=norm(body(raw,source).replace('BINARY_NODE_TAG','0x12'));b=norm(body(log,cut).replace('NJA_digest(log,hash,','hash.digest('));assert a==b,(source,a,b);checks[source]=dict(token_erasure=True,frozen_body_sha256=hashlib.sha256(body(raw,source).encode()).hexdigest())
assert re.search(r'struct SolanaDigest\s*;',program)
(E/'NJA_PARENT_SOURCE.json').write_text(json.dumps(dict(frozen_revision=rev,checks=checks,instance='programs/r1-cost-probe/src/lib.rs::SolanaDigest (unchanged concrete zero-sized type)',program_source_sha256=hashlib.sha256(program.encode()).hexdigest(),cut_sha256=hashlib.sha256(log.encode()).hexdigest(),method='Actual deployed program root and features, local record in place of the opaque digest call; no custom backend type, function pointer, or writable static'),indent=2)+'\n');print('NJA parent source erasure checked at concrete deployed SolanaDigest instance')
