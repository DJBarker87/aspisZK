import KSA_CoImport
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSA

def dotToIsolated (d : LPl_Kit_Release.fast_pairing.canonical.Dot) :
    KSA_Isolated.XRn_Join_Release.fast_pairing.canonical.Dot := ⟨d.sums⟩
theorem dot_push_same (d : LPl_Kit_Release.fast_pairing.canonical.Dot)
    (a b : Array U32 4#usize) :
    KSA_Isolated.fast_pairing.canonical.Dot.push (dotToIsolated d) a b =
    (do
      let d ← fast_pairing.canonical.Dot.push d a b
      ok (dotToIsolated d)) := by
  cases d
  rfl

theorem dot_native (d : FIo_Native.fast_pairing.canonical.Dot)
    (a b : FIo_Native.fast_pairing.canonical.Q) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.push d a b = ok out ∧
      KSA_Isolated.fast_pairing.canonical.Dot.push (dotToIsolated (LPn.DotState.project d)) a b =
      ok (dotToIsolated (LPn.DotState.project out)) := by
  obtain ⟨out,native,model⟩ := LPn.Dot.native_result d a b
  refine ⟨out,native,?_⟩
  rw [dot_push_same,model]
  rfl
#print axioms dot_push_same
#print axioms dot_native
end KSA
