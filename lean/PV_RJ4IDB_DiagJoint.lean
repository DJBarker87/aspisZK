import PV_RJ4IDB_ClientTrace
set_option autoImplicit false
namespace PV_RJ4IDB
variable {S A B : Type}
/-- Consume the existing joint coupling, including exposed final state. This
is not a new simulator, new coins, or a product of marginal laws. -/
theorem coupled_decoder (rel : S → S → Prop) (expose : S → List (Bytes × Bytes))
 (stateLaw : ∀ s t, rel s t → expose s = expose t)
 (x y : PV_DIAG3.Execution S A) (h : PV_DIAG3.Coupled rel x y) :
 decoder (diagWithState expose x) = decoder (diagWithState expose y) := by
 have hs := stateLaw x.state y.state h.2.1
 have he := h.1
 have ht := h.2.2
 simp only [diagWithState,he,ht,hs]

theorem coupled_continuation_decoder (rel : S → S → Prop)
 (expose : S → List (Bytes × Bytes))
 (stateLaw : ∀ s t, rel s t → expose s = expose t)
 (x y : PV_DIAG3.Execution S A) (f g : A → PV_DIAG3.Op S B)
 (h : PV_DIAG3.Coupled rel x y)
 (leaves : ∀ a s t, rel s t → PV_DIAG3.Coupled rel (f a s) (g a t)) :
 decoder (diagWithState expose (PV_DIAG3.bind x f)) =
 decoder (diagWithState expose (PV_DIAG3.bind y g)) :=
 coupled_decoder rel expose stateLaw _ _ (PV_DIAG3.coupled_bind rel x y f g h leaves)
#print axioms coupled_decoder
#print axioms coupled_continuation_decoder
end PV_RJ4IDB
