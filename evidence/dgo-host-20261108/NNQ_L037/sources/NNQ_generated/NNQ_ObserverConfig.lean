import NNQ_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result

theorem observer_withDigest {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
    (id : S2W_ExtractionBoundary.Program) :
    ARQ_Observer.select (A := A) (withDigest c o) id = ARQ_Observer.select c id := by
  funext out
  unfold ARQ_Observer.select
  rw [sdk_withDigest]
  exact observe_op43 _ o id out
#print axioms observer_withDigest
end AspisR1.NNQ_HostDigest
end
