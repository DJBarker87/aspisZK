import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_289
open RSL PCM
def RowSpec (impl : PlannedMarker → Env → Obs Bytes) : Prop :=
  ∀ a env, impl a env = ⟨.ret a.encoded_marker,[]⟩

theorem rejects_const_abort (a : PlannedMarker) :
    ¬ RowSpec (fun _ _ => ⟨.abort,[]⟩) := by
  intro h
  have he := h a env0
  cases he
#print axioms rejects_const_abort
end PCM_POOL_289
