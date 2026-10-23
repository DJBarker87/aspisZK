"""Check only the listed source-slot substitutions; no Rust/binary refinement claim."""
from pathlib import Path
import hashlib,re,subprocess,sys
r=Path(__file__).resolve().parent
ex=r.parent/'s9-actual-ten-round-caller-extraction-v1-20261023'
assert ex.is_dir(), 'missing pinned actual-caller extraction packet'
subprocess.run([sys.executable,str(ex/'check_packet.py')],check=True)
owner=r/'sources/ActualSemanticRoundsEmittedCallerV1.lean'
raw=ex/'raw-generated/Funs.lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(owner)=='af769b5cc0ba3feed529baa8b639ed6660bd77bfaf01c704476916fd47ee7a08'
assert sha(raw)=='127f99ca32c5cb010a8247fa77cfdb06b59523de74b948f996bf243e6907d4be'
s=raw.read_text();a=s.index('def r1_semantic.semantic_rounds\n');b=s.rindex('end AspisR1ActualSemanticRoundCutV1');selected=s[a:b].strip()
assert selected.count('r1_wire.ValidatedRecord.decode_k 1#usize vr 0#usize')==1
assert selected.count('aspis_core.field.QM31.ZERO')==1
assert len(re.findall(r'\br1_semantic\.semantic_round\b',selected))==10
selected=selected.replace('def r1_semantic.semantic_rounds','def emittedSemanticRounds (B : Hooks) (zeroResult : Result QM)')
selected=selected.replace('r1_wire.ValidatedRecord.decode_k 1#usize vr 0#usize','B.decode 1#usize vr 0#usize')
selected=selected.replace('aspis_core.field.QM31.ZERO','zeroResult')
selected=re.sub(r'\br1_semantic\.semantic_round\b','semanticRound B',selected)
s=owner.read_text();a=s.index('def emittedSemanticRounds ');b=s.index('private theorem bind_success',a)
assert selected==s[a:b].strip(), 'caller body differs beyond listed slot substitutions'
assert 'theorem emitted_success_has_initial' in s and 'theorem emitted_success_all_alpha_reads_canonical' in s
print('PASS: exact fresh emitted caller body with only 1decode, 1constant-Result and10same-round slot substitutions; no control-flow/ordering rewrite. Primitive/runtime/release refinement remains open.')
