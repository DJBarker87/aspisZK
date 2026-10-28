import NCM_Opening

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_OpeningView
open Aeneas Aeneas.Std Result NCE_OpeningCuts

/-- Logical value observer for the borrowed opening. It is not a runtime
allocation, copy, or substitute native backing buffer. -/
def read (reader : Reader) (s : Carrier) (i : Usize) : Result (Slice U8 × Carrier) :=
  match readWindow reader i.val 832 0 s with
  | .ok out => if h : out.1.length = 832 then
      ok (⟨out.1,by rw [h];scalar_tac⟩,out.2) else .div
  | .fail error => .fail error
  | .div => .div

/-- Native byte fragments identify the observer with the actual checked
range value, on the SAME proof and complete caller carrier. -/
theorem observation (reader : Reader) (cut : NCE_Native_Opening reader)
    (s : Carrier) (i : Usize) (size : s.proof.val.length = 57607) (bound : i.val < 22) :
    ∃ view, Port4B_Opening.opening s.proof i = ok view ∧ view.val.length = 832 ∧
      read reader s i = ok (view,s) := by
  obtain ⟨view,source,len,returned⟩ := NCM_Opening.observation reader cut s i size bound
  refine ⟨view,source,len,?_⟩
  simp only [read,returned,dif_pos len]
  rfl

#print axioms observation
end AspisR1.NCM_OpeningView
end
