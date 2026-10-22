import R1Z.ProverCommitCircleRows49
import R1Z.ProverCommitBasisFillValue47
/-! Complete four-stage circle-factor fill, via an arbitrary interval invariant. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCircleFill49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitCircleRows49
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open AspisCircleTensorBinding

def model (base : QM31Exact) (d : Nat) : Fin 4 → QM31Exact :=
  ![1,doubledFactor base (2*d-1),doubledFactor base (2*d),
    doubledFactor base (2*d-1)*doubledFactor base (2*d)]

attribute [local irreducible] matrix ProverCommitQArray48.array ProverCommitNativeQ48.source

theorem fill_value (base : QM31Exact) (rows : Nat → Nat → Old.Q)
    (hcrows : ∀ d k, d<5 → k<4 → Canonical (rows d k))
    (n : Nat) (d : Usize) (left : U8) (hleft : left.val=n)
    (positive : 1≤d.val) (bound : d.val+n≤5) (x : Old.Q) (hx : Canonical x)
    (hxd : decode x=doubledFactor base (2*d.val-1)) :
    ∃ out : Nat → Nat → Old.Q, factors.lines (matrix rows) d left (ProverCommitNativeQ48.source x)=
        ok (matrix out) ∧
      (∀ i k, i<5 → k<4 → Canonical (out i k)) ∧
      ∀ i : Fin 5, ∀ k : Fin 4, decode (out i.val k.val)=
        if d.val ≤ i.val ∧ i.val<d.val+n then model base i.val k else decode (rows i.val k.val) := by
  induction n generalizing rows d left x with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨rows,?_,hcrows,?_⟩
    · rw [factors.lines,hz];rfl
    · intro i k;rw [if_neg (by omega)]
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    have hinc : (Usize.wrapping_add d 1#usize).val=d.val+1 := by
      simpa only [show (1#usize).val=1 from rfl] using
        ProverCommitBasisFillValue47.add_val d 1#usize (by change d.val+1<2048;omega)
    obtain ⟨y,hy,hcy,hdy⟩ := ProverCommitFactors49.double_exact x hx
    have hyval : decode y=doubledFactor base (2*d.val) := by
      rw [hdy,hxd,←AspisV5FriNaturalBasisRadix4.doubledFactor_add]
      congr 1 <;> omega
    obtain ⟨row,hrow,hcrow,hdrow⟩ := line_exact x y hx hcy
    obtain ⟨next,hnext,hcnext,hdnext⟩ := ProverCommitFactors49.double_exact y hcy
    have hnval : decode next=doubledFactor base (2*(Usize.wrapping_add d 1#usize).val-1) := by
      rw [hdnext,hyval,←AspisV5FriNaturalBasisRadix4.doubledFactor_add,hinc]
      congr 1 <;> omega
    let changed := Function.update rows d.val row
    have hcchanged : ∀ i k, i<5 → k<4 → Canonical (changed i k) := by
      intro i k hi hk
      by_cases he : i=d.val
      · subst i;simpa only [changed,Function.update_self] using hcrow k hk
      · simpa only [changed,Function.update_of_ne he] using hcrows i k hi hk
    have hrval (k : Fin 4) : decode (row k.val)=model base d.val k := by
      rw [hdrow k,hxd,hyval]
      rfl
    obtain ⟨out,hout,hcout,hdout⟩ := ih changed hcchanged _ _ hdec (by rw [hinc];omega)
      (by rw [hinc];omega) next hcnext hnval
    refine ⟨out,?_,hcout,?_⟩
    · rw [factors.lines]
      simp only [hn,if_false,hy,hrow,bind_tc_ok]
      rw [matrix_update rows d (by omega) row]
      simp only [hnext,lift,bind_tc_ok]
      exact hout
    · intro i k
      rw [hdout,hinc]
      by_cases he : i.val=d.val
      · rw [if_neg (by omega),if_pos (by omega)]
        simp only [changed,he,Function.update_self,hrval]
      · by_cases ht : d.val+1 ≤ i.val ∧ i.val<d.val+1+n
        · rw [if_pos ht,if_pos (by omega)]
        · rw [if_neg ht,if_neg (by omega)]
          simp only [changed,Function.update_of_ne he]

#print axioms fill_value
end R1Z.ProverCommitCircleFill49
