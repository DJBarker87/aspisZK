import NGM_ReferenceLinear
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGM_DoubleModel
open FIn_WeightsExtract

def words (p : field.QM31) : Array U32 4#usize :=
  Array.make 4#usize [p.c0.a,p.c0.b,p.c1.a,p.c1.b]

def Canonical (p : field.QM31) : Prop :=
  p.c0.a.val < NGM_ReferenceLinear.P ∧ p.c0.b.val < NGM_ReferenceLinear.P ∧
  p.c1.a.val < NGM_ReferenceLinear.P ∧ p.c1.b.val < NGM_ReferenceLinear.P

/-- Only a callee-result law is assumed. A native bridge still needs the two
actual multiplication observations and their deterministic SAME-input law. -/
theorem observed (x p : field.QM31) (canonical : Canonical p)
    (product : field.QM31.mul x x = ok p) :
    NGM_DoubleRef.double_observed_ref (words p) (words p) =
      (do let q ← FIn_WeightsExtract.double x;ok (words q)) := by
  obtain ⟨h0,h1,h2,h3⟩ := canonical
  obtain ⟨a,ha,hac⟩ := NGM_ReferenceLinear.add_canonical _ _ h0 h0
  obtain ⟨b,hb,hbc⟩ := NGM_ReferenceLinear.add_canonical _ _ h1 h1
  obtain ⟨c,hc,hcc⟩ := NGM_ReferenceLinear.add_canonical _ _ h2 h2
  obtain ⟨d,hd,hdc⟩ := NGM_ReferenceLinear.add_canonical _ _ h3 h3
  have hz : (0#u32).val < NGM_ReferenceLinear.P := by change 0 < (2147483647:Nat);omega
  have ho : (1#u32).val < NGM_ReferenceLinear.P := by change 1 < (2147483647:Nat);omega
  simp [NGM_DoubleRef.double_observed_ref,words,Array.index_usize,Array.make,
    NGM_ReferenceLinear.add,NGM_ReferenceLinear.sub,
    FIn_WeightsExtract.double,product,field.QM31.add,field.CM31.add,
    field.QM31.sub,field.CM31.sub,field.QM31.ONE,ha,hb,hc,hd,
    h0,h1,h2,h3,hac,hbc,hcc,hdc,hz,ho]
#print axioms observed
end NGM_DoubleModel
