import AspisR1DelayedDots.Funs
import ExtractedCurrentReducer
import CuSavingsResidues

/-! Candidate 4: exact emitted scalar operations, with overflow and residue
facts. No optimized/reference equality is assumed as a primitive. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsDelayedScalar
open Aeneas Aeneas.Std Result
open AspisR1DelayedDots
open AspisV8R17.RawReducer
open ExtractedCurrentReducerOps
open CuSavingsResidues

theorem reducer_eq (x : U64) :
    field.reduce_u64 x = AspisR1Qm31ArithmeticProbe.field.reduce_u64 x := by
  simp only [field.reduce_u64,field.P,
    AspisR1Qm31ArithmeticProbe.field.reduce_u64,AspisR1Qm31ArithmeticProbe.field.P]

theorem reducer_mod (x : U64) :
    ∃ z : U32, field.M31.reduce_u64 x = .ok z ∧ z.val = x.val % P ∧ z.val < P := by
  obtain ⟨z,hr,hm,hc⟩ := ExtractedCurrentReducer.current_reduce_mod x
  refine ⟨z,?_,hm,hc⟩
  simp only [field.M31.reduce_u64,reducer_eq,hr,bind_tc_ok]

theorem add_mod (a b : U32) (ha : a.val < P) (hb : b.val < P) :
    ∃ z : U32, field.M31.add a b = .ok z ∧ z.val = (a.val+b.val)%P ∧ z.val < P := by
  have hf : a.val+b.val < 2^UScalarTy.U32.numBits := by
    change a.val < 2147483647 at ha
    change b.val < 2147483647 at hb
    change a.val+b.val < 4294967296
    omega
  obtain ⟨s,hs,hsv⟩ := tryMk_success (a.val+b.val) hf
  have hadd : a+b = .ok s := hs
  have hP : field.P.val = P := by rfl
  by_cases hc : P ≤ s.val
  · obtain ⟨z,hz,hzv⟩ := sub_success s field.P (by rw [hP];exact hc)
    refine ⟨z,?_,?_,?_⟩
    · simp only [field.M31.add,hadd,bind_tc_ok]
      rw [if_pos (by simpa only [UScalar.ge_equiv,hP] using hc),hz]
    · rw [hzv,hP,hsv]
      have hlo : P ≤ a.val+b.val := by omega
      have hhi : a.val+b.val-P < P := by omega
      symm
      rw [Nat.mod_eq_sub_mod hlo,Nat.mod_eq_of_lt hhi]
    · rw [hzv,hP];omega
  · refine ⟨s,?_,?_,by omega⟩
    · simp only [field.M31.add,hadd,bind_tc_ok]
      rw [if_neg (by simpa only [UScalar.ge_equiv,hP] using hc)]
    · rw [hsv,Nat.mod_eq_of_lt (by omega)]

def foldAdd (raw sum : U64) : Result U64 := do
  let hi ← sum >>> 31#i32
  let folded ← (sum &&& 2147483647#u64) + hi
  raw + folded

theorem foldAdd_success (raw sum : U64) (count : Nat)
    (hc : count < 7) (hr : raw.val < (count+1)*FoldBound) :
    ∃ out : U64, foldAdd raw sum = .ok out ∧
      out.val = raw.val + foldBits sum.val ∧ out.val < (count+2)*FoldBound ∧
      out.val%P = (raw.val+sum.val)%P := by
  obtain ⟨folded,hfold,hv⟩ := ExtractedCurrentReducer.foldExecution_success sum
  have hf := fold_bound sum.val sum.bv.isLt
  have hfit : raw.val+folded.val < 2^64 := by
    rw [hv]
    norm_num [FoldBound] at hr hf ⊢
    omega
  obtain ⟨out,ha,hov⟩ := add_success raw folded hfit
  refine ⟨out,?_,by rw [hov,hv],?_,?_⟩
  · have heq : (do let hi ← sum >>> 31#i32
                  (sum &&& 2147483647#u64) + hi) = .ok folded := by
      simpa only [ExtractedCurrentReducer.foldExecution,
        ExtractedCurrentReducer.mask64,ExtractedCurrentReducer.mask32] using hfold
    unfold foldAdd
    rw [←bind_assoc_eq,heq,bind_tc_ok,ha]
  · rw [hov,hv];omega
  · rw [hov,hv,Nat.add_mod,fold_mod,←Nat.add_mod]

theorem decoded_canonical (bytes : Array U8 4#usize) (x : U32)
    (h : (do let o ← field.M31.from_le_bytes bytes
             core.option.Option.unwrap o) = .ok x) : x.val < P := by
  simp only [field.M31.from_le_bytes,bind_tc_ok] at h
  split at h
  · cases h
  · rename_i hc
    simp only [core.option.Option.unwrap] at h
    cases h
    have hp : field.P.val = P := rfl
    have hn : ¬ P ≤ (core.num.U32.from_le_bytes bytes).val := by
      simpa only [UScalar.ge_equiv,hp] using hc
    omega

#print axioms reducer_mod
#print axioms add_mod
#print axioms foldAdd_success
#print axioms decoded_canonical
end AspisR1.CuSavingsDelayedScalar
