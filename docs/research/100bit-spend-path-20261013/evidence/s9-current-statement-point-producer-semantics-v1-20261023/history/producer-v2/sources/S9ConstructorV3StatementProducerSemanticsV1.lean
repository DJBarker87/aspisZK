import S9ConstructorV3InitialSuccessorSemanticsV1
import S9ConstructorV3DecodedInputV1
import S9ConstructorV3StatementProducerCanonicalV1
import S9ConstructorV3QMAddSubSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3StatementProducerSemanticsV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3CarryBodySemanticsV1
open AspisR1S9ConstructorV3VectorMeaningV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ConstructorV3StatementProducerCanonicalV1
open AspisR1S9ConstructorV3DecodedInputV1
open AspisR1S9ActualWeightsNewBoxNewV3

def PointsMeaning (points : StatementPoints) (p : Nat → Nat → ExactQM) : Prop :=
  ∀ (k : Usize) (row : Vector), Array.index_usize points k = .ok row → Meaning row (p k.val)

def xor12Point (p : Nat → ExactQM) (i : Nat) : ExactQM :=
  if i=7 ∨ i=6 then 1-p i else p i

theorem make3_points_meaning (a b c : Vector)
    (p0 p1 p2 : Nat → ExactQM) (ha : Meaning a p0) (hb : Meaning b p1) (hc : Meaning c p2) :
    PointsMeaning (Array.make 3#usize [a,b,c]) (fun k => if k=0 then p0 else if k=1 then p1 else p2) := by
  intro k row hread i q hq
  have hkbound := index_success_bound (Array.make 3#usize [a,b,c] : StatementPoints) k row hread
  have hthree : (3#usize).val = 3 := by decide
  have hkcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases hkcases with hk0 | hk1 | hk2
  · have hk : k = 0#usize := UScalar.eq_of_val_eq (by simpa using hk0)
    subst k
    change Result.ok a = Result.ok row at hread
    have he : a = row := Result.ok.inj hread
    subst row
    simpa only [PointsMeaning,if_pos rfl] using ha i q hq
  · have hk : k = 1#usize := UScalar.eq_of_val_eq (by simpa using hk1)
    subst k
    change Result.ok b = Result.ok row at hread
    have he : b = row := Result.ok.inj hread
    subst row
    simpa using hb i q hq
  · have hk : k = 2#usize := UScalar.eq_of_val_eq (by simpa using hk2)
    subst k
    change Result.ok c = Result.ok row at hread
    have he : c = row := Result.ok.inj hread
    subst row
    simpa using hc i q hq

/-- Complete accepted execution of the generated source cut: derives its own
carry result, both complement writes, and input decode interface. The source
cut's iterator normalization and Box/runtime boundaries are retained. -/
theorem statement_points_success_exact (z : Vector) (points : StatementPoints)
    (hz : VectorCanonical z)
    (hsource : state_only_prefix.r0.statement_points z = .ok points) :
    PointsMeaning points (fun k => if k=0 then decodedInput z
      else if k=1 then successorPoint (decodedInput z) else xor12Point (decodedInput z)) := by
  let p := decodedInput z
  have hzMean : Meaning z p := decoded_input_meaning z
  unfold state_only_prefix.r0.statement_points state_only_prefix.state_only_statement_points at hsource
  obtain ⟨s,hs,hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨iter,hiter,hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨successor,hsuccessor,hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨q,hq,hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨q1,hq1,hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨absorption,ha,hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨q2,hq2,hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨q3,hq3,hsource⟩ := bind_success_inv _ _ _ hsource
  obtain ⟨absorption1,ha1,hsource⟩ := bind_success_inv _ _ _ hsource
  have hsEq : Array.to_slice z = s := Result.ok.inj hs
  subst s
  have hlen : Slice.len (Array.to_slice z)=10#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len,Array.to_slice,z.property]
  rw [hlen] at hiter
  have hiEq : iter = (⟨{start:=0#usize,«end»:=10#usize}⟩ : ReverseRange) := by
    change .ok (⟨{start:=0#usize,«end»:=10#usize}⟩ : ReverseRange)=.ok iter at hiter
    exact (Result.ok.inj hiter).symm
  subst iter
  have hsucc := AspisR1S9ConstructorV3InitialSuccessorSemanticsV1.initial_successor_loop_exact
    p z successor _ hz hzMean rfl rfl hsuccessor
  have hone : Can field.QM31.ONE := AspisR1S9ConstructorV3Loop1CellCanonicalV1.one_canonical
  have honeDecode : decode field.QM31.ONE=1 := AspisR1S9ConstructorTensorFactorMapV1.ctor_one_decode
  have hqc : Can q := raw_read_canonical z 7#usize q hz hq
  obtain ⟨hc1,hd1⟩ := AspisR1S9ConstructorV3QMAddSubSemanticsV1.generated_sub_success_exact
    field.QM31.ONE q q1 hone hqc hq1
  change decode q1=decode field.QM31.ONE-decode q at hd1
  have hqVal : decode q=p 7 := hzMean 7#usize q hq
  rw [honeDecode,hqVal] at hd1
  have hmabs := update_meaning z absorption 7#usize q1 p hzMean ha
  have hseven : (7#usize).val=7 := rfl
  have hsix : (6#usize).val=6 := rfl
  simp only [hseven,hd1] at hmabs
  have hac := vector_update_canonical z absorption 7#usize q1 hz hc1 ha
  have hq2c : Can q2 := raw_read_canonical absorption 6#usize q2 hac hq2
  obtain ⟨hc3,hd3⟩ := AspisR1S9ConstructorV3QMAddSubSemanticsV1.generated_sub_success_exact
    field.QM31.ONE q2 q3 hone hq2c hq3
  change decode q3=decode field.QM31.ONE-decode q2 at hd3
  have hq2Val : decode q2=p 6 := by
    have h := hmabs 6#usize q2 hq2
    simpa only [hsix,Function.update_of_ne (by decide : (6:Nat)≠7)] using h
  rw [honeDecode,hq2Val] at hd3
  have hmabs1 := update_meaning absorption absorption1 6#usize q3
    (Function.update p 7 (1-p 7)) hmabs ha1
  simp only [hsix,hd3] at hmabs1
  have hfun : Function.update (Function.update p 7 (1-p 7)) 6 (1-p 6)=xor12Point p := by
    funext i
    by_cases h7 : i=7 <;> by_cases h6 : i=6 <;>
      simp [xor12Point,Function.update,h7,h6]
  rw [hfun] at hmabs1
  have hout : Array.make 3#usize [z,successor,absorption1]=points := Result.ok.inj hsource
  subst points
  exact make3_points_meaning z successor absorption1 p (successorPoint p) (xor12Point p)
    hzMean hsucc.2 hmabs1

#print axioms statement_points_success_exact
end AspisR1S9ConstructorV3StatementProducerSemanticsV1
