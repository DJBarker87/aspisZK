import R1Z.ProverCommitSparseBits50
/-! Entire owned sparse-prefix product, for every prefix length through ten.
The scalar condition and each actual field operation are discharged. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSparseWeight50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitSampleBits49
open ProverCommitSparseBits50 (selected)
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

def factorValue (p : Nat → Old.Q) (pref : Usize) (w i : Nat) : QM31Exact :=
  if bit pref w i then decode (p i) else 1-decode (p i)

def product (p : Nat → Old.Q) (pref : Usize) (w : Nat) : Nat → Nat → QM31Exact
 | 0,_ => 1
 | n+1,i => factorValue p pref w i*product p pref w n (i+1)

attribute [local irreducible] ProverCommitQArray48.array ProverCommitNativeQ48.source product factorValue

theorem weight (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i))
    (pref : Usize) (width : U8) (hw : width.val≤10) (n : Nat) (i : Usize)
    (left : U8) (hleft : left.val=n) (bound : i.val+n≤width.val)
    (acc : Old.Q) (hacc : Canonical acc) :
    ∃ z : Old.Q, sparse50.weight (ProverCommitQArray48.array 10#usize p) pref width i left
      (ProverCommitNativeQ48.source acc)=ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=decode acc*product p pref width.val n i.val := by
  induction n generalizing i left acc with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨acc,?_,hacc,?_⟩
    · rw [sparse50.weight,hz];rfl
    · rw [product,mul_one]
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    have hinc : (core.num.Usize.wrapping_add i 1#usize).val=i.val+1 := by
      change (Usize.wrapping_add i 1#usize).val=_
      simpa only [show (1#usize).val=1 from rfl] using
        ProverCommitBasisFillValue47.add_val i 1#usize (by change i.val+1<2048;omega)
    obtain ⟨f,hf,hcf,hvf⟩ := ProverCommitSparseBits50.factor (p i.val) (hp _ (by omega)) (selected width i pref)
    have hcond := ProverCommitSparseBits50.condition width i pref (by omega) hw
    have hfv : decode f=factorValue p pref width.val i.val := by
      rw [hvf,factorValue]
      cases hb : bit pref width.val i.val
      · rw [if_pos (hcond.mpr hb)];rfl
      · have hnot : selected width i pref≠0#usize := by
          intro h;have hfalse := hcond.mp h;rw [hb] at hfalse;cases hfalse
        rw [if_neg hnot];rfl
    obtain ⟨next,hnext,hcnext,hvnext⟩ := ProverCommitNativeQ48.mul acc f hacc hcf
    obtain ⟨z,hz,hcz,hdz⟩ := ih _ _ hdec (by rw [hinc];omega) next hcnext
    refine ⟨z,?_,hcz,?_⟩
    · rw [sparse50.weight]
      simp only [hn,if_false,lift,bind_tc_ok]
      rw [ProverCommitQArray48.index 10#usize p i (by change i.val<10;omega)]
      simp only [bind_tc_ok]
      change (do
        let f ← sparse50.factor (ProverCommitNativeQ48.source (p i.val)) (selected width i pref)
        let next ← field.QM31.mul (ProverCommitNativeQ48.source acc) f
        sparse50.weight (ProverCommitQArray48.array 10#usize p) pref width
          (core.num.Usize.wrapping_add i 1#usize) (U8.wrapping_sub left 1#u8) next)=_
      rw [hf];simp only [bind_tc_ok,hnext]
      exact hz
    · rw [hdz,hvnext,hfv,hinc,product]
      exact mul_assoc _ _ _

#print axioms weight
end R1Z.ProverCommitSparseWeight50
