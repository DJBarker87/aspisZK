from pathlib import Path
import re,json,hashlib,subprocess
w=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
p=json.loads((w/'extraction/input/source-pins.json').read_text())
original=(w/'extraction/input/original-push.rs.txt').read_text()
loop="""            for j in 0..4 {
                self.sums[j]=self.sums[j].wrapping_add(
                    (raw[j]&u64::from(P)).wrapping_add(raw[j]>>31));
            }"""
unrolled='\n'.join(f'            self.sums[{j}]=self.sums[{j}].wrapping_add((raw[{j}]&u64::from(P)).wrapping_add(raw[{j}]>>31));' for j in range(4))
assert loop in original
candidate=original.replace(loop,unrolled)
assert candidate in (w/'extraction/input/lib.rs').read_text()
for name in ['Types','Funs']:
 t=(w/'extraction/generated/AspisR1DotPushLocal'/(name+'.lean')).read_text()
 t=re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth) .+\n','',t,flags=re.M)
 if name=='Funs':
  t=t.replace('import AspisR1DotPushLocal.FunsExternal\n','')
  t=t.replace('def canonical.Dot.push\n','def canonical.Dot.push\n  (rawFn : canonical.Q → canonical.Q → Result (Array Std.U64 4#usize))\n')
  t=t.replace('let raw1 ← canonical.Q.raw a b','let raw1 ← rawFn a b')
  t=t.replace('def dot_push_entry\n','def dot_push_entry\n  (rawFn : canonical.Q → canonical.Q → Result (Array Std.U64 4#usize))\n')
  t=t.replace('canonical.Dot.push dot a b','canonical.Dot.push rawFn dot a b')
  t+='\n#print axioms AspisR1DotPushLocal.canonical.Dot.push\n'
 assert t==(w/'sources/AspisR1DotPushLocal'/(name+'.lean')).read_text()
repo=next(q for q in w.parents if (q/'.git').exists())
frozen=subprocess.check_output(['git','-C',str(repo),'show',p['revision']+':crates/aspis-r1-cost-probe/src/fast_pairing.rs'])
assert sha(frozen)==p['source_files']['crates/aspis-r1-cost-probe/src/fast_pairing.rs']
for cut in p['cuts']:assert sha(frozen[cut['start_byte']:cut['end_byte_exclusive']])==cut['sha256']
print('complete original-loop→literal-unroll and emitted-body→rawFn adapter source checks pass; structural, not semantic Rust equivalence')
