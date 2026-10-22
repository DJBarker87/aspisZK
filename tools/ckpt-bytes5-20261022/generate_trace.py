#!/usr/bin/env python3
from pathlib import Path
R=Path(__file__).resolve().parents[2]
L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'RawTx2ResumeDigestCalls.lean').read_text()
proof=s[s.index('  unfold verifier.resumeWithOps at success'):s.index('\n#print axioms resume_bind_success')]
proof=proof.replace('⟨size, _, h⟩','⟨size, hsize, h⟩',1)
names=['hsizebad','hmagicbad','htagbad','hversionbad','hanybad']
for name in names:
    proof=proof.replace('obtain ⟨_, h⟩ := checkpoint_guard _ _ _ h',f'obtain ⟨{name}, h⟩ := checkpoint_guard _ _ _ h',1)
for value,name in [('header','hheader'),('magicBad','hmagic'),('tagByte','htagbyte'),('tag','htag'),('nextByte','hnext'),('version','hversion'),('reserved','hreserved'),('iter','hiter'),('anyResult','hany')]:
    # source uses magicBad? inspect actual name
    proof=proof.replace(f'⟨{value}, _, h⟩',f'⟨{value}, {name}, h⟩',1)
proof=proof.replace('have h := checkpoint_guard_prop _ _ _ h','obtain ⟨hnextbad, h⟩ := checkpoint_guard_prop _ _ _ h')
proof=proof.replace('  obtain ⟨checksumBad, hcb, h⟩', '  have htail := h\n  obtain ⟨checksumBad, hcb, h⟩')
proof=proof.replace('  exact ⟨{','  refine ⟨{')
proof=proof.replace('checksumEqual := ne_sound storedChecksum checksumDigest (hchecksumBad ▸ hcb) }⟩','checksumEqual := ne_sound storedChecksum checksumDigest (hchecksumBad ▸ hcb) }, ?_⟩')
proof+='''
  simp only [program,run_bind,run_lift,run_read,run_pure,run_ite]
  simp only [Aeneas.Std.uncurry,hsize,bind_tc_ok,hsizebad,Bool.false_eq_true,if_false,
    hheader,hmagic,hmagicbad,htagbyte,htag,htagbad,hnext,if_neg hnextbad,
    hversion,hversionbad,hreserved,hiter,hany,hanybad,hend,hstored,hchunks,
    hdigest,hbad,hb,hsp,hpp,hpd,hpb,hpublicBad,hsc,hdomain,hbody,hcp,hcd]
  change (do let value ← tail ops bytes v nextByte end1 storedChecksum checksumDigest;
             ok (value,((before ++ [(chunks,digest)]) ++ [(publicParts,publicDigest)]) ++
                [(checksumParts,checksumDigest)])) = _
  have ht : tail ops bytes v nextByte end1 storedChecksum checksumDigest = ok (.Ok (p,acc)) := htail
  rw [ht]
  simp only [bind_tc_ok,List.append_assoc,List.cons_append,List.nil_append]
'''
text='''import CheckpointBytes5Resume
import RawTx2ResumeDigestCalls
import OraclePortCkptAbiTry
set_option autoImplicit false
namespace AspisR1.CheckpointBytes5Trace
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes5Effect CheckpointBytes5Resume
open OraclePortCkptAbiTry (bind_success)

private theorem checkpoint_guard {T : Type} (b : Bool)
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if b then ok (.Err verifier.Error.Checkpoint) else tail) = ok (.Ok out)) :
    b = false ∧ tail = ok (.Ok out) := by
  cases b
  · exact ⟨rfl,h⟩
  · cases h

private theorem checkpoint_guard_prop {T : Type} (b : Prop) [Decidable b]
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if b then ok (.Err verifier.Error.Checkpoint) else tail) = ok (.Ok out)) :
    ¬ b ∧ tail = ok (.Ok out) := by
  split at h
  · cases h
  · exact ⟨by assumption,h⟩

/-- The complete successful source schedule has exactly these three reads.
The pre-existing Calls inventory is now accompanied by an execution equation. -/
theorem successful_log (ops : ResumeOps) {H : Type}
    (digestInst : aspis_core.digest.Digest32 H)
    (ne_sound : ∀ (s : Slice U8) (a : Array U8 32#usize),
      ops.ne core.cmp.PartialEqU8 s a = ok false → s.val = a.val)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator) (before : Log)
    (success : verifier.resumeWithOps ops digestInst bytes proof public1 v hash =
      ok (.Ok (p,acc))) : ∃ c : Tx2ResumeDigests.Calls digestInst hash bytes proof public1,
    run digestInst hash (program ops bytes proof public1 v) before =
      ok (.Ok (p,acc), before ++ [(c.proofParts,c.proofDigest),
        (c.publicParts,c.publicDigest),(c.checksumParts,c.checksumDigest)]) := by
'''+proof.replace('resume_bind_success','bind_success')+'''
#print axioms checkpoint_guard
#print axioms checkpoint_guard_prop
#print axioms successful_log
end AspisR1.CheckpointBytes5Trace
'''
(L/'CheckpointBytes5Trace.lean').write_text(text)
