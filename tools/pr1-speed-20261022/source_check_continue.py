from pathlib import Path
import hashlib,json,subprocess,re,sys
r=Path(__file__).resolve().parents[2];base='4209a51d40a59a285601db28a3122a01f84e9510'
paths=['docs/research/v8-r0-zk-20261009/c3/check/src/native_m31.rs','docs/research/v8-r0-zk-20261009/c3/check/src/lib.rs','docs/research/v8-r0-zk-20261009/c3/build/src/lib.rs','docs/research/v8-r0-zk-20261009/z4/z9c.rs','docs/research/v8-r0-zk-20261009/z4/z9d.rs']
# Preserve the exact original checked dot/kdot, reached by large-shape fallback.
def body(s,name):
 a=s.index('fn '+name+'(');a=s.index('{',a);b=a+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
p=paths[1];old=subprocess.check_output(['git','show',base+':'+p],text=True);new=(r/p).read_text()
for f in ['dot','kdot']:assert body(old,f)==body(new,f)
reference=(r/'tools/pr1-speed-20261022/stage2-gates/reference_check.rs').read_text();assert reference==old
assert 'if s <= native_m31::MAX_TERMS' in new and 'if len <= native_m31::MAX_TERMS' in new
kernel=(r/paths[0]).read_text();harness=(r/'tools/pr1-speed-20261022/stage2-gates/gates.rs').read_text()
assert 'if x >= y { x - y } else { x + P as u32 - y }' in kernel
assert 'if x >= y { x - y } else { x + P as u32 - y }' in harness
# Check all frozen verifier/program sources; changed dependencies are host-only.
changes=subprocess.check_output(['git','diff',base,'--name-only','--','crates','programs'],text=True).splitlines();assert not changes,changes
print(json.dumps(dict(baseline=base,checks=['original checked dot/kdot preserved','runtime reference byte-identical to baseline','explicit accumulator bound guards','per-step subtraction source expression bound','all crates and programs unchanged'],source_sha256={p:hashlib.sha256((r/p).read_bytes()).hexdigest()for p in paths},limitations='Kani local arithmetic and bounded traversal; general independent-coordinate composition is analytical, not whole-program equivalence.'),indent=2))
