from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
src=Path('crates/aspis-r1-cost-probe/src/sim.rs')
s=src.read_text();h=(E/'harness/oracle-effect26.rs').read_text()
for part in [s[s.index('fn concat('):s.index('\n/// Answers every read')],
             s[s.index('struct CoinState'):s.index('\n/// Programs exactly one read')]]:
 assert part in h
(E/'oracle-effect-source.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_file=str(src),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),harness_sha256=hashlib.sha256(h.encode()).hexdigest(),copied_exact=['concat','CoinState','CoinOracle::digest'],result='Concrete counterexample to an unconditional stateless interpretation; not an end-to-end security counterexample'),indent=2)+'\n')
