#!/usr/bin/env python3
"""Read-only exact source/emission reuse audit; no S4 candidate is modified."""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[2]
P=R/'docs/research/100bit-spend-path-20261013'
S=P/'evidence/s4-solanadigest-wrapper-p3-binding-v1-20261022'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def body(text,needle):
 start=text.index(needle);start=text.index('{',start);depth=1;i=start+1
 while depth:
  depth+=(text[i]=='{')-(text[i]=='}');i+=1
 return text[start+1:i-1].strip()
native=R/'programs/r1-cost-probe/src/lib.rs'
old=S/'source-snapshots/production-lib.rs'
fragment=body(native.read_text(),'fn digest(')
assert fragment==body(old.read_text(),'fn digest(')=='hashv(parts).to_bytes()'
funs=S/'generated/AspisR1SolanaDigestWrapperCut/Funs.lean'
adapt=S/'sources/S4SolanaDigestWrapperP3BindingV1.lean'
def block(s,name):
 i=s.index('def '+name);j=s.find('/--',i)
 return s[i:] if j<0 else s[i:j]
def rhs(s):return re.search(r':= do\n(.*?)(?=\n(?:/--|def |end |$))',s,re.S).group(1).rstrip()
emitted=rhs(block(funs.read_text(),'SolanaDigest.Insts.Aspis_coreDigestDigest32.digest'))
expected='  let h ← solana_sha256_hasher.hashv parts\n  solana_hash.Hash.to_bytes h'
assert emitted==expected,repr(emitted)
assert rhs(block(funs.read_text(),'solana_hash.Hash.to_bytes'))=='  ok self'
model=P/'lean/S2W_DigestExtraction.lean'
assert rhs(block(model.read_text(),'digest'))==expected.replace('solana_sha256_hasher.hashv parts','hashv parts').replace('solana_hash.Hash.to_bytes h','toBytes h')
assert rhs(block(model.read_text(),'toBytes'))=='  ok self'
assert 'def solana_hash.Hash := Array Std.U8 32#usize' in (S/'generated/AspisR1SolanaDigestWrapperCut/Types.lean').read_text()
lock=(R/'Cargo.lock').read_text()
assert re.search(r'name = "solana-hash"\nversion = "2.3.0"',lock)
assert re.search(r'name = "solana-sha256-hasher"\nversion = "2.3.0"',lock)
items=[native,old,funs,S/'generated/AspisR1SolanaDigestWrapperCut/Types.lean',adapt,S/'extraction-runs/charon-v4/receipt.json',model,R/'Cargo.lock']
record={'status':'pass','qualification':'Reuse only unchanged three-line method and Hash::to_bytes extraction syntax; not the S4 cone theorem or its concrete native installation. Charon004 current-root attempt failed and is excluded. D188 extraction correspondence is explicit in the new structure.','native_body':fragment,'emitted_rhs':emitted,'model_substitutions':['SolanaDigest unit carrier reused from AdapterRw','hashv opaque callee made explicit parameter','Hash nominal alias is Array U8 32; retain exact to_bytes body'],'sources':{str(p.relative_to(R)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in items}}
out=R/'evidence/s2w-20261023/digest-source-reuse.json'
if '--check' in sys.argv:assert json.loads(out.read_text())==record
else:out.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'pass','body':fragment,'pins':len(items)}))
