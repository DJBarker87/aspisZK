import FJd_PointReference
import FJc_WeightValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_SourceFactor
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues
/-- Straight-line arithmetic of ONE constructor digit, not a loop replay. -/
def reference (a b : SQ) : Result (List SQ) := do
  let na ← FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE a
  let nb ← FIn_WeightsExtract.field.QM31.sub FIn_WeightsExtract.field.QM31.ONE b
  let f0 ← FIn_WeightsExtract.field.QM31.mul na nb
  let f1 ← FIn_WeightsExtract.field.QM31.mul a nb
  let f2 ← FIn_WeightsExtract.field.QM31.mul na b
  let f3 ← FIn_WeightsExtract.field.QM31.mul a b
  ok [f0,f1,f2,f3]

theorem value (a b : SQ) (out : List SQ) (ha : Canon a) (hb : Canon b)
    (run : reference a b=ok out) :
    (∀ x∈out,Canon x) ∧
    out.map decode=[(1-decode a)*(1-decode b),decode a*(1-decode b),
      (1-decode a)*decode b,decode a*decode b] := by
  unfold reference at run
  obtain ⟨na,hna,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨nb,hnb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨f0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨f1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨f2,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨f3,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have hna' := FJc_WeightValues.sub _ _ _ FJc_WeightConstants.one.1 ha hna
  have hnb' := FJc_WeightValues.sub _ _ _ FJc_WeightConstants.one.1 hb hnb
  have v0 := FJc_WeightValues.mul _ _ _ hna'.1 hnb'.1 h0
  have v1 := FJc_WeightValues.mul _ _ _ ha hnb'.1 h1
  have v2 := FJc_WeightValues.mul _ _ _ hna'.1 hb h2
  have v3 := FJc_WeightValues.mul _ _ _ ha hb h3
  cases Result.ok.inj run
  constructor
  · intro x hx
    simp only [List.mem_cons,List.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact v0.1
    · exact v1.1
    · exact v2.1
    · exact v3.1
  · simp only [List.map_cons,List.map_nil,v0.2,v1.2,v2.2,v3.2,hna'.2,hnb'.2,
      FJc_WeightConstants.one.2]
#print axioms value
end AspisR1.FJd_SourceFactor
end
