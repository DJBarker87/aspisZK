import R1Z.ProverCommitSampleModel49
/-! Semantic challenge positions and round-prefix preservation, including
source sample/tail writes before the next alpha assignment. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitChallengePrefix55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open R0Z.HonestView

def withSemantic (ch : Challenges QM31Exact) (sem : Nat → Old.Q) : Challenges QM31Exact :=
  {ch with sem := fun i => decode (sem i.val)}

def Prefix (sem p : Nat → Old.Q) (r : Nat) : Prop :=
  ∀ i : Fin 10, i.val<r → decode (p i.val)=decode (sem (15+i.val))

theorem alpha_source (ch : Challenges QM31Exact) (sem : Nat → Old.Q) (i : Fin 10) :
    alpha (withSemantic ch sem) i=decode (sem (15+i.val)) := rfl

theorem initial (sem p : Nat → Old.Q) : Prefix sem p 0 := by
  intro i hi;omega

theorem model_prefix (ch : Challenges QM31Exact) (sem p : Nat → Old.Q) (r : Fin 10)
    (hp : Prefix sem p r.val) :
    ∀ i : Fin 10, i.val<r.val → decode (p i.val)=alpha (withSemantic ch sem) i := hp

def nextPoint (sem p : Nat → Old.Q) (r : Nat) (a : Usize) (sample : U32) : Nat → Old.Q :=
  Function.update (ProverCommitSamplePoint49.point p r a sample) r (sem (15+r))

theorem preserved (sem p : Nat → Old.Q) (r : Fin 10) (hp : Prefix sem p r.val)
    (a : Usize) (sample : U32) : Prefix sem (nextPoint sem p r.val a sample) (r.val+1) := by
  intro i hi
  by_cases he : i.val=r.val
  · simp only [nextPoint,he,Function.update_self]
  · have hpre : i.val<r.val := by omega
    rw [nextPoint,Function.update_of_ne he,
      ProverCommitSamplePoint49.point_decode p r.val r.isLt a sample i.val i.isLt,if_pos hpre]
    exact hp i hpre

def advance (sem p : Nat → Old.Q) (r rem a : Usize) (left : U8) (sample : U32) := do
  let point ← owned.sample (ProverCommitQArray48.array 10#usize p) r sample
  let point ← owned.tail point r rem a 0#usize left
  let alpha ← Array.index_usize (ProverCommitQArray48.array 25#usize sem)
    (Usize.wrapping_add 15#usize r)
  Array.update point r alpha

attribute [local irreducible] ProverCommitQArray48.array ProverCommitNativeQ48.source

theorem source_advance (sem p : Nat → Old.Q) (r rem a : Usize) (left : U8) (sample : U32)
    (hr : r.val<10) (hrem : rem.val=9-r.val) (hleft : left.val=9-r.val) :
    advance sem p r rem a left sample=
      ok (ProverCommitQArray48.array 10#usize (nextPoint sem p r.val a sample)) := by
  have hidx : (Usize.wrapping_add 15#usize r).val=15+r.val := by
    simpa only [show (15#usize).val=15 from rfl] using
      ProverCommitBasisFillValue47.add_val 15#usize r (by change 15+r.val<2048;omega)
  have hp := ProverCommitSamplePoint49.point_result p r rem a left hr hrem hleft sample
  unfold advance
  rw [←bind_assoc,hp]
  simp only [bind_tc_ok]
  rw [ProverCommitQArray48.index _ _ _ (by rw [hidx];change 15+r.val<25;omega)]
  simp only [bind_tc_ok,hidx]
  exact ProverCommitQArray48.update 10#usize _ r hr (sem (15+r.val))

#print axioms alpha_source
#print axioms initial
#print axioms model_prefix
#print axioms preserved
#print axioms source_advance
end R1Z.ProverCommitChallengePrefix55
