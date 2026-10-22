import AspisR1ProducerRelease47.Linear50
import R1Z.ProverCommitLinearMath50
import R1Z.ProverCommitQArray48
import R1Z.ProverCommitBasisCounter47
/-! Complete optimized reverse suffix/weighted-statistic counter. -/
set_option autoImplicit false
namespace R1Z.ProverCommitLinearLoop50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
attribute [local irreducible] ProverCommitQArray48.array ProverCommitNativeQ48.source ProverCommitLinearMath50.stats

theorem go (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (n : Nat) (left : U8) (hl : left.val=n) (bound : n≤10)
    (s w : Old.Q) (hs : Canonical s) (hw : Canonical w) :
    ∃ a b : Old.Q, linear50.go (ProverCommitQArray48.array 10#usize p) left
      (ProverCommitNativeQ48.source s) (ProverCommitNativeQ48.source w)=
        ok (ProverCommitNativeQ48.source a,ProverCommitNativeQ48.source b) ∧
      Canonical a ∧ Canonical b ∧
      (decode a,decode b)=ProverCommitLinearMath50.stats (fun i => decode (p i)) n (decode s) (decode w) := by
  induction n generalizing left s w with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨s,w,?_,hs,hw,?_⟩
    · rw [linear50.go,hz];rfl
    · rw [ProverCommitLinearMath50.stats]
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    let idx := core.convert.num.FromUsizeU8.from (U8.wrapping_sub left 1#u8)
    have hidx : idx.val=n := by scalar_tac
    obtain ⟨next,hnext,hcnext,hdnext⟩ := ProverCommitNativeQ48.add s (p n) hs (hp _ (by omega))
    have hweighted : ∃ v : Old.Q,
        (if U8.wrapping_sub left 1#u8=0#u8 then ok (ProverCommitNativeQ48.source w)
          else field.QM31.add (ProverCommitNativeQ48.source w) (ProverCommitNativeQ48.source next))=
          ok (ProverCommitNativeQ48.source v) ∧ Canonical v ∧
        decode v=if n=0 then decode w else decode w+decode next := by
      by_cases hn0 : n=0
      · have hz : U8.wrapping_sub left 1#u8=0#u8 := by scalar_tac
        exact ⟨w,by rw [if_pos hz],hw,by rw [if_pos hn0]⟩
      · have hz : U8.wrapping_sub left 1#u8≠0#u8 := by scalar_tac
        obtain ⟨v,hv,hcv,hdv⟩ := ProverCommitNativeQ48.add w next hw hcnext
        exact ⟨v,by rw [if_neg hz];exact hv,hcv,by rw [if_neg hn0];exact hdv⟩
    obtain ⟨v,hv,hcv,hdv⟩ := hweighted
    obtain ⟨a,b,hab,hca,hcb,hdab⟩ := ih _ hdec (by omega) next v hcnext hcv
    refine ⟨a,b,?_,hca,hcb,?_⟩
    · rw [linear50.go]
      simp only [hn,if_false,lift,bind_tc_ok]
      rw [ProverCommitQArray48.index 10#usize p idx (by change idx.val<10;rw [hidx];omega)]
      simp only [bind_tc_ok]
      rw [hidx,hnext]
      simp only [bind_tc_ok,hv]
      exact hab
    · rw [hdab,ProverCommitLinearMath50.stats,hdv,hdnext]

#print axioms go
end R1Z.ProverCommitLinearLoop50
