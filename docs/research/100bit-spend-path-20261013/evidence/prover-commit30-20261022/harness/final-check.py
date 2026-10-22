from pathlib import Path
import subprocess,json,hashlib,re,shlex
E=Path(__file__).resolve().parent.parent
rows=[json.loads(s) for s in (E/'rust-receipts.jsonl').read_text().splitlines()]
callers=[r for r in rows if re.fullmatch(r'caller30-row\d\d-context-v1',r['name'])]
assert len(callers)==25
assert {int(r['name'][12:14]) for r in callers}==set(range(25))
assert all(r['exit_status']==0 and r['swaps']==0 for r in callers)
assert all('VERIFICATION:- SUCCESSFUL' in (E/'receipts'/r['name']/'stdout.log').read_text() for r in callers)
assert len({r['source_hashes']['crates/aspis-r1-cost-probe/src/sim.rs'] for r in callers})==1
assert len({r['source_hashes']['crates/aspis-r1-cost-probe/src/r1_wire.rs'] for r in callers})==1
native=Path('crates/aspis-r1-cost-probe/src/sim.rs').read_text()
statement=re.search(r'for row in 0\.\.25u8 \{ (.*?) \}',native).group(1)
harness=(E/'harness/caller-kani30.rs').read_text()
assert statement in harness
bindings={}
for f,marker in [('sim.rs','#[cfg(kani)]\nmod caller_kani30'),('r1_wire.rs','#[cfg(kani)]\npub(crate) mod modular_kani30')]:
 p=E/'rust-sources'/('semantic-'+f+'.txt');text=p.read_text();prefix=text.split(marker)[0]
 tracked=Path('crates/aspis-r1-cost-probe/src')/f
 assert prefix==tracked.read_text(),f
 bindings[f]=dict(tracked_sha256=hashlib.sha256(tracked.read_bytes()).hexdigest(),instrumented_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),native_prefix_byte_identical=True)
shipped=subprocess.check_output(['git','diff','--name-only','e78e2c022','--','crates','programs'],text=True).splitlines()
assert shipped==[],shipped
(E/'caller-matrix.json').write_text(json.dumps(dict(accepted_rows=list(range(25)),count=25,native_statement=statement,bindings=bindings,shipped_files_changed=shipped,wall_seconds_sum=sum(r['wall_seconds'] for r in callers),max_peak_rss_kib=max(r['peak_rss_kib'] for r in callers),max_scope_peak_bytes=max(r['cgroup_memory_peak_bytes'] for r in callers),receipts=[r['name'] for r in callers],trust_boundary='Two-harness contextual congruence: independently verified native/owned callee equality (including effects), plus common arbitrary complete post-state in one-call contexts; standard allocator and Rust library models retained.'),indent=2)+'\n')
print('25/25 caller gates; exact native prefixes and iteration statement; zero shipped edits')
# Full endpoint copies and verbatim statement excerpts.
rel='docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitDeployedFuel22.lean'
before=subprocess.check_output(['git','show','26b922be6:'+rel],text=True);after=Path(rel).read_text();assert before==after
P=E/'endpoint';P.mkdir(exist_ok=True)
for label,s in [('before',before),('after',after)]:
 (P/(label+'.lean.txt')).write_text(s)
 a=s.index('def RustProverRefinement : Prop :=');b=s.index('\n/--',a)
 c=s.index('theorem privacy_headline_deployed\n');d=s.index(' := by',c)
 (P/(label+'-statement.lean.txt')).write_text(s[a:b]+'\n\n'+s[c:d]+'\n')
(P/'identity.json').write_text(json.dumps(dict(base_revision='26b922be6',path=rel,sha256=hashlib.sha256(after.encode()).hexdigest(),byte_identical=True,premises_deleted=0,concrete_experiment_specialized=False),indent=2)+'\n')
(P/'deletion.diff').write_text('')
