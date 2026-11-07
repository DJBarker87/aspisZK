import NMS_Interpreted
set_option autoImplicit false
noncomputable section
namespace NMS_Effect242Fold
open Aeneas Aeneas.Std AdapterRw NMS_RSLRefine
abbrev Effects := NMS_Effect242.Effects RSL.Spec
abbrev Auth := NMS_Effect242.AuthCall RSL.Spec
/-- Every link is a COMPLETE child observation law, at identical typed
arguments. The dictionary is intermediate source composition, not a native
root with arbitrary operations. CLOSED links still require installation. -/
structure Links (actual model : Effects) : Prop where
 first : ∀ {T : Type} (a : Slice T), Refines (actual.op9 a) (model.op9 a)
 lane : ∀ n, Refines (actual.op17 n) (model.op17 n)
 nullifier : ∀ p, Refines (actual.op20 p) (model.op20 p)
 decode : ∀ d, Refines (actual.op23 d) (model.op23 d)
 pubkey : ∀ p, Refines (actual.op37 p) (model.op37 p)
 pool : Refines actual.op45 model.op45
 scan : ∀ d, Refines (actual.op51 d) (model.op51 d)
 reconstruct : ∀ r a c, Refines (actual.op52 r a c) (model.op52 r a c)
 data : ∀ a, Refines (actual.data a) (model.data a)

def AuthLink (actual model : Auth) : Prop :=
 ∀ p a pool lane slot, Refines (actual p a pool lane slot) (model p a pool lane slot)

/-- Actual emitted control, with complete child laws substituted forward.
Returned errors, fail/div, independent stops and every ordered event prefix
are all quantified in Refines; no successful child premise is used. -/
theorem fold (ops : Ops) (actual model : Effects) (children : Links actual model)
 (auth referenceAuth : Auth) (child233 : AuthLink auth referenceAuth)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Refines (NMS_Effect242.validate ops actual auth program accounts data slot)
  (NMS_Effect242.validate ops model referenceAuth program accounts data slot) := by
 unfold NMS_Effect242.validate
 repeat' first
 | (solve | exact children.first _)
 | (solve | exact children.lane _)
 | (solve | exact children.nullifier _)
 | (solve | exact children.decode _)
 | (solve | exact children.pubkey _)
 | (solve | exact children.pool)
 | (solve | exact children.scan _)
 | (solve | exact children.reconstruct _ _ _)
 | (solve | exact children.data _)
 | (solve | exact child233 _ _ _ _ _)
 | (solve | exact refl _)
 | (apply NMS_RSLRefine.bind)
 | intro
 | split
#print axioms fold
end NMS_Effect242Fold
