from pathlib import Path
import hashlib,json,re
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022')
p=H/'src/crates/aspis-r1-cost-probe/src/sim.rs';s=p.read_text();assert 'mod step_kani29' not in s
line=re.search(r'for row in 0\.\.25u8 \{ (.*?) \}',s).group(1)
assert line.count('&r.semantic[row as usize]')==1
shell=line.replace('&r.semantic[row as usize]','&record')
addition=(H/'harness/step-kani29.rs').read_text().replace('NATIVE_ITERATION',shell)
p.write_text(s+'\n'+addition)
q=H/'src/crates/aspis-r1-cost-probe/src/r1_wire.rs'
q.write_text(q.read_text()+'\n#[cfg(kani)] pub fn make_kani29<H:Digest32>(hash:H,state:[u8;32],next_row:u8)->SemanticTranscript<H>{SemanticTranscript{hash,state,next_row}}\n')
(H/'kani-binding.json').write_text(json.dumps(dict(native_statement=line,shell_statement=shell,native_sim_sha256=hashlib.sha256(s.encode()).hexdigest(),instrumented_sim_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),stubbed_functions=[],scope='one iteration; arbitrary row <25, state, semantic array, all record byte arrays of length <=901; exact ordered oracle call replay including errors'),indent=2)+'\n')
