import GeometryInputsEntry
import BatchInverseCanonicalComposition
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GeometryInputs.Proof
open alloc.vec R17CurrentM31Semantics

def NonzeroOutputs (qv : QueryValues) : Prop := ∀ q values z,
  qv q = .ok (.Ok (values,z)) → ∀ x ∈ values.val, decode x ≠ 0

theorem inputTrace_nonzero (qv : QueryValues) (queries : Array U32 22#usize)
    (hnz : NonzeroOutputs qv) (start end1 : Nat) (records : List InputRecord)
    (ht : InputTrace qv queries start end1 records) :
    ∀ x ∈ records.flatMap (fun e => e.1.val), decode x ≠ 0 := by
  induction ht with
  | nil n => simp
  | cons i end1 values z tail hi hq ht ih =>
    intro x hx
    simp only [List.flatMap_cons,List.mem_append] at hx
    rcases hx with hx | hx
    · exact hnz _ values z hq x hx
    · exact ih x hx

/-- Composition of the checked indexed input loop and the checked batch inverse
candidate. Full frozen caller and iterator-to-indexed equivalence are open. -/
def geometryAndInvert (qv : QueryValues) (queries : Array U32 22#usize)
    (start end1 : Usize) : Result (core.result.Result ((Vec M31) × (Vec M31)) GeometryInputsError) := do
  let r ← geometry_inputs_indexed qv queries start end1
  match r with
  | .Err e => ok (.Err e)
  | .Ok (flat,zs) =>
    let inverse ← AspisR1BatchBackward.Proof.runCandidate flat
    ok (.Ok (inverse,zs))

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem geometryAndInvert_success (qv : QueryValues) (queries : Array U32 22#usize)
    (hnz : NonzeroOutputs qv) (start end1 : Usize) (inverse zs : Vec M31)
    (h : geometryAndInvert qv queries start end1 = .ok (.Ok (inverse,zs))) :
    start.val ≤ end1.val ∧ end1.val ≤ 22 ∧
      AspisR1BatchBackward.Proof.CanonicalVec inverse ∧
      ∃ records : List InputRecord, InputTrace qv queries start.val end1.val records ∧
        inverse.val.map decode = ((records.flatMap (fun e => e.1.val)).map decode).map Inv.inv ∧
        zs.val = records.map Prod.snd ∧ records.length = end1.val-start.val ∧
        inverse.val.length = (end1.val-start.val)*5 ∧ zs.val.length = end1.val-start.val := by
  unfold geometryAndInvert at h
  rcases bind_ok_inv h with ⟨r,hr,h⟩
  cases r with
  | Err e => cases h
  | Ok val =>
    rcases val with ⟨flat,zs0⟩
    rcases bind_ok_inv h with ⟨inv0,hinv,h⟩
    have he := core.result.Result.Ok.inj (Result.ok.inj h)
    cases he
    obtain ⟨hs,he,records,ht,hf,hz,hlen,hflat,hzs⟩ :=
      geometry_inputs_success_trace qv queries start end1 flat zs hr
    have hn : ∀ x ∈ flat.val, decode x ≠ 0 := by
      rw [hf]
      exact inputTrace_nonzero qv queries hnz start.val end1.val records ht
    have hc := AspisR1BatchBackward.Proof.runCandidate_success_correct flat inverse hn hinv
    refine ⟨hs,he,hc.1,records,ht,?_,hz,hlen,?_,hzs⟩
    · simpa only [hf] using hc.2
    · have hl := congrArg List.length hc.2
      simp only [List.length_map] at hl
      omega

#print axioms inputTrace_nonzero
#print axioms geometryAndInvert_success
end AspisR1GeometryInputs.Proof
