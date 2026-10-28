import R1Z.PV_RunJoin_SourceSelectionContract
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EndpointSelection
open R0P R0Z.ZkStatement R0Z.FsStatement
local notation "K" => PrivacyR1AcctBasis.K
abbrev h := PV_RunJoin_SourceSelectionContract.endpointHonest
variable {CommitHandle : Type}

/-- Extend the SAME fixed proof-account endpoint selection to the larger
published interface. The extension never claims that an arbitrary other
honest prover has a canonical BuilderSource witness. -/
def selection
    (selected : Statement K CommitHandle → h.Instance → PV_Src_NativeInput.Input)
    (publicRecord : Statement K CommitHandle → PV_Src_NativeInput.Input) :
    PV_RunJoin_InstalledFamily.Selection CommitHandle := by
  classical
  exact {
    selected := fun hh x w => if eq : hh = h then selected x (eq ▸ w) else publicRecord x
    publicRecord := publicRecord }

theorem selected_exact
    (selected : Statement K CommitHandle → h.Instance → PV_Src_NativeInput.Input)
    (publicRecord : Statement K CommitHandle → PV_Src_NativeInput.Input)
    (x : Statement K CommitHandle) (w : h.Instance) :
    (selection selected publicRecord).selected h x w = selected x w := by
  classical
  simp [selection]

theorem public_binding
    (selected : Statement K CommitHandle → h.Instance → PV_Src_NativeInput.Input)
    (publicRecord : Statement K CommitHandle → PV_Src_NativeInput.Input)
    (binding : ∀ x w, h.public w = x.1 →
      PV_Src_NativeInput.publicInput (selected x w) =
        PV_Src_NativeInput.publicInput (publicRecord x)) :
    PV_RunJoin_InstalledFamily.PublicBinding (selection selected publicRecord) := by
  classical
  intro hh x w hw
  by_cases eq : hh = h
  · subst hh
    rw [selected_exact]
    exact binding x w hw
  · change PV_Src_NativeInput.publicInput
        (if eq : hh = h then selected x (eq ▸ w) else publicRecord x) = _
    rw [dif_neg eq]
    rfl

/-- The only public-binding hypothesis now ranges over the actual fixed
endpoint. Its truth and the native association of the chosen input family
remain explicit P obligations. -/
def data
    (selected : Statement K CommitHandle → h.Instance → PV_Src_NativeInput.Input)
    (publicRecord : Statement K CommitHandle → PV_Src_NativeInput.Input)
    (binding : ∀ x w, h.public w = x.1 →
      PV_Src_NativeInput.publicInput (selected x w) =
        PV_Src_NativeInput.publicInput (publicRecord x)) :
    PV_RunJoin_SourceSelectionContract.Data (CommitHandle := CommitHandle) where
  selection := selection selected publicRecord
  publicBinding := public_binding selected publicRecord binding

theorem record_exact
    (selected : Statement K CommitHandle → h.Instance → PV_Src_NativeInput.Input)
    (publicRecord : Statement K CommitHandle → PV_Src_NativeInput.Input)
    (binding : ∀ x w, h.public w = x.1 →
      PV_Src_NativeInput.publicInput (selected x w) =
        PV_Src_NativeInput.publicInput (publicRecord x))
    (x : Statement K CommitHandle) (w : h.Instance) :
    PV_RunJoin_SourceSelectionContract.selectedRecord (data selected publicRecord binding) x w =
      selected x w := selected_exact selected publicRecord x w

#print axioms selected_exact
#print axioms public_binding
#print axioms data
#print axioms record_exact
end R1Z.PV_RunJoin_EndpointSelection
