import AspisR1Post25Sampler.Funs
import R1Z.PV_L2_RecordCompact
set_option autoImplicit false
namespace R1Z.PV_L2_F5DivStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Post25Sampler
open R1Z.PV_L2_Record R1Z.CertCheck
local instance : Bind Recorded := ⟨@PV_L2_RecordCompact.bind⟩

def step (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    Result (Array U32 8#usize × U64 × Usize) := do
  let j1 ← j-1#usize
  let i ← remainder <<< 32#i32
  let i1 ← Array.index_usize rank j1
  let i2 ← lift (core.convert.num.FromU64U32.from i1)
  let dividend ← lift (i ||| i2)
  let divisor ← lift (core.convert.num.FromU64U32.from field.P)
  let quotient ← dividend / divisor
  let word ← lift (UScalar.cast .U32 quotient)
  let rank1 ← Array.update rank j1 word
  let divisor1 ← lift (core.convert.num.FromU64U32.from field.P)
  let remainder1 ← dividend % divisor1
  ok (rank1,remainder1,j1)

/-- Site 201 records integer division's full dividend/divisor pair. Site
202 is the corresponding remainder. Raw source words are not discarded. -/
def recorded (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    Recorded (Array U32 8#usize × U64 × Usize) := do
  let j1 ← operation (.guard 200 j.val 1 true) (j-1#usize)
  let i ← operation (.guard 203 remainder.val 32 true) (remainder <<< 32#i32)
  let i1 ← operation (.index 0 j1.val) (Array.index_usize rank j1)
  let i2 := core.convert.num.FromU64U32.from i1
  let dividend := i ||| i2
  let divisor := core.convert.num.FromU64U32.from field.P
  let quotient ← operation (.guard 201 dividend.val divisor.val true) (dividend/divisor)
  let word := UScalar.cast .U32 quotient
  let rank1 ← operation (.index 1 j1.val) (Array.update rank j1 word)
  let divisor1 := core.convert.num.FromU64U32.from field.P
  let remainder1 ← operation (.rem dividend.val divisor1.val) (dividend%divisor1)
  PV_L2_Record.pure (rank1,remainder1,j1)

theorem erases (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    (recorded rank remainder j).value = step rank remainder j := by
  simp only [recorded,step,PV_L2_RecordCompact.bind_value,operation_value,
    PV_L2_Record.pure_value,lift,bind_tc_ok]

theorem source_body (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    sampler.qm31_div_pass_loop.body rank remainder j = if j>0#usize then (do
      let after ← step rank remainder j
      ok (cont after)) else ok (done (rank,remainder)) := by
  rw [sampler.qm31_div_pass_loop.body]
  split
  · simp only [step,bind_assoc_eq,bind_tc_ok]
  · rfl

theorem decrease (rank : Array U32 8#usize) (remainder : U64) (j : Usize)
    (after : Array U32 8#usize × U64 × Usize) (success : step rank remainder j=ok after) :
    after.2.2.val=j.val-1 ∧ 1≤j.val := by
  unfold step at success
  obtain ⟨j1,hj1,success⟩ := bind_eq_ok success
  obtain ⟨i,hi,success⟩ := bind_eq_ok success
  obtain ⟨i1,hi1,success⟩ := bind_eq_ok success
  obtain ⟨i2,hi2,success⟩ := bind_eq_ok success
  obtain ⟨dividend,hd,success⟩ := bind_eq_ok success
  obtain ⟨divisor,hv,success⟩ := bind_eq_ok success
  obtain ⟨quotient,hq,success⟩ := bind_eq_ok success
  obtain ⟨word,hw,success⟩ := bind_eq_ok success
  obtain ⟨rank1,hr,success⟩ := bind_eq_ok success
  obtain ⟨divisor1,hv1,success⟩ := bind_eq_ok success
  obtain ⟨remainder1,hm,success⟩ := bind_eq_ok success
  have he := ok_inj success
  rw [←he]
  simpa only [show (1#usize).val=1 from rfl] using sub_ok hj1

#print axioms erases
#print axioms source_body
#print axioms decrease
end R1Z.PV_L2_F5DivStep
