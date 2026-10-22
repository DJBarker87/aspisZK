import AspisR1ProducerRelease47.Mle50
import R1Z.ProverCommitSparseWidth50
import R1Z.ProverCommitSparseSuffix50
import R1Z.ProverCommitBooleanEnum49
/-! Native MLE caller parameters are produced with exact bounds and Boolean
suffix values, rather than supplied as caller hypotheses. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSparseParams50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

theorem count (width : U8) (hw : width.val≤10) :
    ∃ c : U16, mle50.count width=ok c ∧ c.val=2^width.val := by
  let cast := core.convert.num.FromU32U8.from width
  let c := core.num.U16.wrapping_shl 1#u16 cast
  have hcast : cast.val=width.val := by scalar_tac
  refine ⟨c,by rw [mle50.count];rfl,?_⟩
  change ((1#u16).bv <<< (cast.val%UScalarTy.U16.numBits)).toNat=_
  rw [BitVec.toNat_shiftLeft]
  change (1 <<< (cast.val%16))%65536=2^width.val
  rw [hcast,Nat.mod_eq_of_lt (show width.val<16 by omega),Nat.shiftLeft_eq,Nat.one_mul]
  apply Nat.mod_eq_of_lt
  have hp : 2^width.val≤2^10 := Nat.pow_le_pow_right (by decide) hw
  omega

theorem parameters (p : Nat → Old.Q) (hp : ∀ i, i<10 → Canonical (p i)) :
    ∃ (width trailing : U8) (suffix : Usize),
      sparse_scan50.width (ProverCommitQArray48.array 10#usize p) 10#u8=ok width ∧
      trailing=U8.wrapping_sub 10#u8 width ∧
      sparse_scan50.suffix (ProverCommitQArray48.array 10#usize p)
        (core.convert.num.FromUsizeU8.from width) trailing=ok suffix ∧
      width.val+trailing.val=10 ∧ suffix.val<2^trailing.val ∧
      (∀ j : Fin trailing.val, decode (p (width.val+j.val))=
        if suffix.val.testBit (trailing.val-1-j.val) then 1 else 0) := by
  obtain ⟨width,hw,hwb,hbool,hmax⟩ := ProverCommitSparseWidth50.width p 10 10#u8 rfl (by decide)
  let trailing := U8.wrapping_sub 10#u8 width
  have htr : trailing.val=10-width.val := by
    dsimp only [trailing]
    rw [U8.wrapping_sub_val_eq,UScalar.size_def]
    change (10+(256-width.val))%256=10-width.val
    omega
  have hsum : width.val+trailing.val=10 := by omega
  let start := core.convert.num.FromUsizeU8.from width
  have hstart : start.val=width.val := by scalar_tac
  obtain ⟨suffix,hs,hsv,hsb⟩ := ProverCommitSparseSuffix50.suffix p trailing.val trailing rfl start
    (by rw [hstart];omega)
  refine ⟨width,trailing,suffix,hw,rfl,hs,hsum,hsb,?_⟩
  intro j
  have hi : width.val+j.val<10 := by have := j.isLt;omega
  have hb : ProverCommitSparsePredicate50.rawBool (p (width.val+j.val))=true :=
    hbool _ (by omega) hi
  have hbit : ProverCommitBooleanEnum49.tail trailing.val ⟨suffix.val,hsb⟩ j=
      ProverCommitSparsePredicate50.rawOne (p (width.val+j.val)) := by
    change suffix.val.testBit (trailing.val-1-j.val)=_
    rw [hsv]
    simpa only [hstart] using R0P.rowCode_testBit trailing.val
      (fun i => ProverCommitSparsePredicate50.rawOne (p (start.val+i.val))) j
  change decode (p (width.val+j.val))=
    if ProverCommitBooleanEnum49.tail trailing.val ⟨suffix.val,hsb⟩ j then 1 else 0
  rw [hbit]
  exact ProverCommitSparsePredicate50.boolean_value _ (hp _ hi) hb

#print axioms count
#print axioms parameters
end R1Z.ProverCommitSparseParams50
