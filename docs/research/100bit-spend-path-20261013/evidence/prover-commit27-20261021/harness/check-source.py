from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
s=Path('crates/aspis-r1-cost-probe/src/sim.rs').read_text()
r=Path('crates/aspis-r1-cost-probe/src/r1_wire.rs').read_text()
t=Path('crates/aspis-r1-cost-probe/src/transcript.rs').read_text()
h=(E/'harness/oracle27.rs').read_text();c=(E/'harness/callers27.rs').read_text()
exact=[s[s.index('fn concat('):s.index('\n/// Answers every read')],s[s.index('struct CoinState'):s.index('\n/// Programs exactly one read')]]
for body in exact:assert body in h
start=r.index('    fn sample_block_validated(');end=r.index('    fn sample_block(',start)
assert r[start:end].replace('    fn sample_block_validated','    pub fn sample_block_validated') in c
start=t.index('    pub fn absorb(');end=t.index('    pub fn scalar(',start)
assert t[start:end] in c
start=t.index('        self.absorb(row,payload);',t.index('    pub fn queries('));end=t.index('        let (q,state)=',start)
assert t[start:end] in c
assert t[start:end].count('self.hash.digest(')==16
assert 'fn digest(&mut self,parts:&[&[u8]])->[u8;32]' in c
pins={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in [Path('crates/aspis-r1-cost-probe/src/sim.rs'),Path('crates/aspis-r1-cost-probe/src/r1_wire.rs'),Path('crates/aspis-r1-cost-probe/src/transcript.rs'),E/'harness/oracle27.rs',E/'harness/effect27.rs',E/'harness/callers27.rs']}
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),pins=pins,exact_copied=['concat','CoinState and CoinOracle::digest','sample_block_validated (visibility change only)','Transcript::absorb and block','queries prefix through all sixteen digest reads'],interface_change='Owned caller trait uses &mut self and returns updated hash in extraction. Original pure generated dictionaries unchanged.',scope='Literal call skeletons and per-call reference gate. Does not bind complete validator/decoder/trace/retry/serialization continuations or either FSExperiment.')
(E/'source-binding.json').write_text(json.dumps(result,indent=2)+'\n')
print('Source excerpts and exact eager query schedule: PASS')
