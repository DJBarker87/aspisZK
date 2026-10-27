import RPt_FIp_DotsAllCanonical
import RPz7_FIp_DotsAdapter
import SAQ_WideABI
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_DotsOutputCanonical
open Aeneas Aeneas.Std Result

theorem fromNative (x : FIo_Install.NE) (h : FIo_WideValues.Canon x) :
    Port4C_QueryArithmetic.CanonE (FIo_Install.fromE x) := by
  apply (SAQ_WideABI.w_canonical _).mpr
  exact h

theorem all (q : Slice U8) (g : Array FIp_DotsAdapter.E 29#usize) (out : Array FIp_DotsAdapter.E 4#usize)
    (run : FIp_DotsAdapter.dots q g=ok out) :
    ∀ x∈out.val,Port4C_QueryArithmetic.CanonE x := by
  obtain ⟨native,hn,he⟩ := FIp_DotsAdapter.reached q g out run
  subst out
  have hcan := FIp_DotsAllCanonical.four q (FIp_DotsAdapter.toArray g) native hn
  intro x hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  exact fromNative y (hcan y hy)

#print axioms fromNative
#print axioms all
end AspisR1.FIp_DotsOutputCanonical
end
