from pathlib import Path
import hashlib,json,re
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022')
p=H/'src/crates/aspis-r1-cost-probe/src/sim.rs';s=p.read_text();assert 'mod step_kani29' not in s
line=re.search(r'for row in 0\.\.25u8 \{ (.*?) \}',s).group(1)
assert line.count('&r.semantic[row as usize]')==1
shell=line
addition=(H/'harness/step-kani29.rs').read_text().replace('NATIVE_ITERATION',shell)
p.write_text(s+'\n'+addition)
q=H/'src/crates/aspis-r1-cost-probe/src/r1_wire.rs'
q.write_text(q.read_text()+'\n#[cfg(kani)] pub fn make_kani29<H:Digest32>(hash:H,state:[u8;32],next_row:u8)->SemanticTranscript<H>{SemanticTranscript{hash,state,next_row}}\n')
(H/'kani-binding.json').write_text(json.dumps(dict(native_statement=line,shell_statement=shell,native_sim_sha256=hashlib.sha256(s.encode()).hexdigest(),instrumented_sim_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),stubbed_functions=["crate::sampler::qm31_sample → shared_sample"],sampler_summary="Arbitrary common output; both input blocks and call counts must agree. This is a congruence cut for the same retained pure total sampler, not a hash assumption.",scope='one native iteration including Records vector lookup; concrete selected row <25, arbitrary state, semantic array, selected record bytes of length <=901; 27-record constructor invariant; exact ordered three-read oracle framing including errors'),indent=2)+'\n')
