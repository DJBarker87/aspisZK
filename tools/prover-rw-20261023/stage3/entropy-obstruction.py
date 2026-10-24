"""Pin the actual native/emitted call sites behind the formal counterexample.
This is source inspection plus a tiny tape example, not an OS RNG experiment.
"""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/stage3'
p=R/'crates/aspis-prover/src/state_only_entropy.rs';s=p.read_text()
a=s.index('    pub fn generate_for_mask_nonce(');b=s.index('\n    pub fn mask_nonce',a)
source=s[a:b]
assert 'Zeroizing::new([0u8; 64])' in source and 'getrandom::fill(bytes.as_mut())?' in source
assert 'retry+=1' in source and 'ENTROPY_RETRY_LIMIT: usize = 16' in s
name='aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body'
def decl(text):
 blocks=text.split('/-- ')
 hits=[('/-- '+b).rstrip()+'\n' for b in blocks[1:] if re.search(r'\bdef\s+'+re.escape(name)+r'\b',b)]
 assert len(hits)==1;return hits[0]
raw=decl((E/'11224.lean.txt').read_text())
normalized=decl((R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean').read_text())
# 11224 is the initial parameterized body before the lift qualification.
assert normalized.replace('Aeneas.Std.lift','lift')==raw
zero=bytes(64);nonzero=bytes([1])*64
trace=[]
for i,block in enumerate([zero,nonzero]):
 accepted=any(block[:32]) and any(block[32:])
 trace.append(dict(cursor=i,input_buffer='00'*64,output_block=block.hex(),result='success' if accepted else 'retry'))
 if accepted:break
sha=lambda t:hashlib.sha256(t.encode()).hexdigest()
x=dict(qualification='Native source inspection and source-control tape example; not an actual OS call, compiler theorem or probability/experiment closure',native_source=str(p.relative_to(R)),native_file_sha256=sha(s),native_function_sha256=sha(source),native_function=source,raw_emitted_body_sha256=sha(raw),normalized_body_sha256=sha(normalized),entropy_body_unchanged_except_lift_qualification=True,external_signature='getrandom.fill : Slice U8 -> Result ((core.result.Result Unit getrandom.error.Error) * Slice U8)',dictionary_field='ExternalFuns.op129',tape_example=trace,formal_obstruction='R1Z.ProverRwEntropyIteration.no_retry_then_success',primitive_obstruction='R1Z.ProverRwEntropyObstruction.no_two_draw_dictionary',accepted_attempts=[11255,11260,11261],false_claim='A fixed pure external dictionary faithfully represents every native E1 iteration and ordered fill-result history for every admitted fixed coin tape.',not_refuted=['Native Rust correctness','Privacy','Conjunct 1 with an effect-aware or proved observational transport'],required_repair='Thread explicit RNG/oracle/IO state through the extraction interpretation, or prove an observational transport that preserves the unchanged realBad, realSeedQueries and joint L1/L2 law. A pure dictionary plus opaque contracts cannot prove the contradicted stronger iteration equation.')
(E/'entropy-obstruction.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:x[k] for k in ['entropy_body_unchanged_except_lift_qualification','formal_obstruction','false_claim']}))
