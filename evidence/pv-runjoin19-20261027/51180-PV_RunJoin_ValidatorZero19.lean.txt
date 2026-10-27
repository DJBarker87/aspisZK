import R1Z.PV_RunJoin_IndexedPair19
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ValidatorZero19
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
abbrev CS := {s : State // Canonical s}

theorem total (s : CS) (r : Fin 22) : ∃ out : State,
    poseidon2.apply_round_by_index s.val (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)) = ok (some (),out) ∧ Canonical out := by
  obtain ⟨out,ho,_⟩ := apply_round_lift (K := PV_RunJoin_FixtureRecords.M) s.val
    (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)) (by simpa using r.isLt)
  refine ⟨out,?_,fun j => apply_round_canon _ _ out ho j.val j.isLt⟩
  rw [PV_RunJoin_IndexedCopy19.source s.val s.property r,ho]
  rfl
#print axioms total

def next (s : CS) (r : Fin 22) : CS := ⟨Classical.choose (total s r),(Classical.choose_spec (total s r)).2⟩
theorem next_eq (s : CS) (r : Fin 22) :
    poseidon2.apply_round_by_index s.val (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)) = ok (some (),(next s r).val) :=
  (Classical.choose_spec (total s r)).1
#print axioms next_eq

def zero : CS := ⟨Array.repeat 16#usize 0#u32,by intro j; fin_cases j <;> decide⟩
theorem leading_total : ∃ out : State, poseidon2.external_linear_lazy zero.val = ok out ∧ Canonical out := by
  obtain ⟨out,ho,hc,_⟩ := PV_Src_ExternalModel.source (K := PV_RunJoin_FixtureRecords.M) zero.val
  exact ⟨out,by rw [PV_Src_ExternalReference.call_eq];exact ho,hc⟩
#print axioms leading_total

def s0 : State := zero.val
def lead : CS := ⟨Classical.choose leading_total,(Classical.choose_spec leading_total).2⟩
def s1 : State := lead.val
theorem external : poseidon2.external_linear_lazy s0 = ok s1 := (Classical.choose_spec leading_total).1
#print axioms external
def c2 : CS := next lead ⟨0,by decide⟩
def s2 : State := c2.val
theorem step0 : poseidon2.apply_round_by_index s1 0#usize = ok (some (),s2) := next_eq lead ⟨0,by decide⟩
#print axioms step0
def c3 : CS := next c2 ⟨1,by decide⟩
def s3 : State := c3.val
theorem step1 : poseidon2.apply_round_by_index s2 1#usize = ok (some (),s3) := next_eq c2 ⟨1,by decide⟩
#print axioms step1
def c4 : CS := next c3 ⟨2,by decide⟩
def s4 : State := c4.val
theorem step2 : poseidon2.apply_round_by_index s3 2#usize = ok (some (),s4) := next_eq c3 ⟨2,by decide⟩
#print axioms step2
def c5 : CS := next c4 ⟨3,by decide⟩
def s5 : State := c5.val
theorem step3 : poseidon2.apply_round_by_index s4 3#usize = ok (some (),s5) := next_eq c4 ⟨3,by decide⟩
#print axioms step3
def c6 : CS := next c5 ⟨4,by decide⟩
def s6 : State := c6.val
theorem step4 : poseidon2.apply_round_by_index s5 4#usize = ok (some (),s6) := next_eq c5 ⟨4,by decide⟩
#print axioms step4
def c7 : CS := next c6 ⟨5,by decide⟩
def s7 : State := c7.val
theorem step5 : poseidon2.apply_round_by_index s6 5#usize = ok (some (),s7) := next_eq c6 ⟨5,by decide⟩
#print axioms step5
def c8 : CS := next c7 ⟨6,by decide⟩
def s8 : State := c8.val
theorem step6 : poseidon2.apply_round_by_index s7 6#usize = ok (some (),s8) := next_eq c7 ⟨6,by decide⟩
#print axioms step6
def c9 : CS := next c8 ⟨7,by decide⟩
def s9 : State := c9.val
theorem step7 : poseidon2.apply_round_by_index s8 7#usize = ok (some (),s9) := next_eq c8 ⟨7,by decide⟩
#print axioms step7
def c10 : CS := next c9 ⟨8,by decide⟩
def s10 : State := c10.val
theorem step8 : poseidon2.apply_round_by_index s9 8#usize = ok (some (),s10) := next_eq c9 ⟨8,by decide⟩
#print axioms step8
def c11 : CS := next c10 ⟨9,by decide⟩
def s11 : State := c11.val
theorem step9 : poseidon2.apply_round_by_index s10 9#usize = ok (some (),s11) := next_eq c10 ⟨9,by decide⟩
#print axioms step9
def c12 : CS := next c11 ⟨10,by decide⟩
def s12 : State := c12.val
theorem step10 : poseidon2.apply_round_by_index s11 10#usize = ok (some (),s12) := next_eq c11 ⟨10,by decide⟩
#print axioms step10
def c13 : CS := next c12 ⟨11,by decide⟩
def s13 : State := c13.val
theorem step11 : poseidon2.apply_round_by_index s12 11#usize = ok (some (),s13) := next_eq c12 ⟨11,by decide⟩
#print axioms step11
def c14 : CS := next c13 ⟨12,by decide⟩
def s14 : State := c14.val
theorem step12 : poseidon2.apply_round_by_index s13 12#usize = ok (some (),s14) := next_eq c13 ⟨12,by decide⟩
#print axioms step12
def c15 : CS := next c14 ⟨13,by decide⟩
def s15 : State := c15.val
theorem step13 : poseidon2.apply_round_by_index s14 13#usize = ok (some (),s15) := next_eq c14 ⟨13,by decide⟩
#print axioms step13
def c16 : CS := next c15 ⟨14,by decide⟩
def s16 : State := c16.val
theorem step14 : poseidon2.apply_round_by_index s15 14#usize = ok (some (),s16) := next_eq c15 ⟨14,by decide⟩
#print axioms step14
def c17 : CS := next c16 ⟨15,by decide⟩
def s17 : State := c17.val
theorem step15 : poseidon2.apply_round_by_index s16 15#usize = ok (some (),s17) := next_eq c16 ⟨15,by decide⟩
#print axioms step15
def c18 : CS := next c17 ⟨16,by decide⟩
def s18 : State := c18.val
theorem step16 : poseidon2.apply_round_by_index s17 16#usize = ok (some (),s18) := next_eq c17 ⟨16,by decide⟩
#print axioms step16
def c19 : CS := next c18 ⟨17,by decide⟩
def s19 : State := c19.val
theorem step17 : poseidon2.apply_round_by_index s18 17#usize = ok (some (),s19) := next_eq c18 ⟨17,by decide⟩
#print axioms step17
def c20 : CS := next c19 ⟨18,by decide⟩
def s20 : State := c20.val
theorem step18 : poseidon2.apply_round_by_index s19 18#usize = ok (some (),s20) := next_eq c19 ⟨18,by decide⟩
#print axioms step18
def c21 : CS := next c20 ⟨19,by decide⟩
def s21 : State := c21.val
theorem step19 : poseidon2.apply_round_by_index s20 19#usize = ok (some (),s21) := next_eq c20 ⟨19,by decide⟩
#print axioms step19
def c22 : CS := next c21 ⟨20,by decide⟩
def s22 : State := c22.val
theorem step20 : poseidon2.apply_round_by_index s21 20#usize = ok (some (),s22) := next_eq c21 ⟨20,by decide⟩
#print axioms step20
def c23 : CS := next c22 ⟨21,by decide⟩
def s23 : State := c23.val
theorem step21 : poseidon2.apply_round_by_index s22 21#usize = ok (some (),s23) := next_eq c22 ⟨21,by decide⟩
#print axioms step21
theorem pair0 : poseidon2.evaluate_trace_round_pair s0 0#usize = ok (some (s2,s3)) := by
  apply PV_RunJoin_IndexedPair19.source s0 s1 s2 s3 0#usize (by decide)
  · rw [if_pos rfl]; exact external
  · have hi : Usize.wrapping_mul 2#usize 0#usize = 0#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step0
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 0#usize) 1#usize = 1#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step1
#print axioms pair0
theorem pair1 : poseidon2.evaluate_trace_round_pair s3 1#usize = ok (some (s4,s5)) := by
  apply PV_RunJoin_IndexedPair19.source s3 s3 s4 s5 1#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 1#usize = 2#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step2
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 1#usize) 1#usize = 3#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step3
#print axioms pair1
theorem pair2 : poseidon2.evaluate_trace_round_pair s5 2#usize = ok (some (s6,s7)) := by
  apply PV_RunJoin_IndexedPair19.source s5 s5 s6 s7 2#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 2#usize = 4#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step4
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 2#usize) 1#usize = 5#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step5
#print axioms pair2
theorem pair3 : poseidon2.evaluate_trace_round_pair s7 3#usize = ok (some (s8,s9)) := by
  apply PV_RunJoin_IndexedPair19.source s7 s7 s8 s9 3#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 3#usize = 6#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step6
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 3#usize) 1#usize = 7#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step7
#print axioms pair3
theorem pair4 : poseidon2.evaluate_trace_round_pair s9 4#usize = ok (some (s10,s11)) := by
  apply PV_RunJoin_IndexedPair19.source s9 s9 s10 s11 4#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 4#usize = 8#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step8
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 4#usize) 1#usize = 9#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step9
#print axioms pair4
theorem pair5 : poseidon2.evaluate_trace_round_pair s11 5#usize = ok (some (s12,s13)) := by
  apply PV_RunJoin_IndexedPair19.source s11 s11 s12 s13 5#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 5#usize = 10#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step10
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 5#usize) 1#usize = 11#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step11
#print axioms pair5
theorem pair6 : poseidon2.evaluate_trace_round_pair s13 6#usize = ok (some (s14,s15)) := by
  apply PV_RunJoin_IndexedPair19.source s13 s13 s14 s15 6#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 6#usize = 12#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step12
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 6#usize) 1#usize = 13#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step13
#print axioms pair6
theorem pair7 : poseidon2.evaluate_trace_round_pair s15 7#usize = ok (some (s16,s17)) := by
  apply PV_RunJoin_IndexedPair19.source s15 s15 s16 s17 7#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 7#usize = 14#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step14
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 7#usize) 1#usize = 15#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step15
#print axioms pair7
theorem pair8 : poseidon2.evaluate_trace_round_pair s17 8#usize = ok (some (s18,s19)) := by
  apply PV_RunJoin_IndexedPair19.source s17 s17 s18 s19 8#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 8#usize = 16#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step16
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 8#usize) 1#usize = 17#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step17
#print axioms pair8
theorem pair9 : poseidon2.evaluate_trace_round_pair s19 9#usize = ok (some (s20,s21)) := by
  apply PV_RunJoin_IndexedPair19.source s19 s19 s20 s21 9#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 9#usize = 18#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step18
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 9#usize) 1#usize = 19#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step19
#print axioms pair9
theorem pair10 : poseidon2.evaluate_trace_round_pair s21 10#usize = ok (some (s22,s23)) := by
  apply PV_RunJoin_IndexedPair19.source s21 s21 s22 s23 10#usize (by decide)
  · rw [if_neg (by decide)]
  · have hi : Usize.wrapping_mul 2#usize 10#usize = 20#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step20
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize 10#usize) 1#usize = 21#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step21
#print axioms pair10
end R1Z.PV_RunJoin_ValidatorZero19
