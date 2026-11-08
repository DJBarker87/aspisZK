import PV_THR2_BoxRegister
import PV_OWN2_Exports
set_option autoImplicit false
noncomputable section
namespace PV_THR2_SourceOwnership
open PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_EVHB_OwnerHeap
open PV_OWN2_Codec PV_OWN2_FreshAllocation
open PV_STX2_Syntax PV_STX2_SliceSyntax

/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Select the callback Box::new destination from f361 statement13923. -/
def callbackDestination : Option PV_STX2_Syntax.Place :=
  match PV_THR2_F361.node125 with
  | .leaf (.call _ _ _ destination _) => some destination
  | _ => none

/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
The earlier generated Box call binds local39, not a supplied capture place. -/
theorem callback_destination : callbackDestination = some (.local 39) := rfl

/-- Conditional on owner acceptance of amended translator. Hypotheses:
none. Instantiate the full named SourceInitBoxOwnership export at the two
generated destinations. The earlier callback lifetime is selected by the
pre-state receiver; absence remains absence. All conditional fields of the
provider contract are retained. This is not entry reachability or OwnInit. -/
theorem source_export {W Attr Data Native IoError OsString Scope : Type}
    (carrier : PV_STX2_Store.Carrier W PV_STX2_Syntax.Data)
    (c : PV_STX2_SliceMachine.Config) (w : W) (s : OWNER)
    (resources : Resources) (encode : Encode) (granted : GrantedRegions) :
    ∀ cid ch, receiver s ⟨c.frame.activation,[39]⟩ = some (cid,ch) →
      PV_OWN2_ExportContracts.SourceOwnership
        (Attr := Attr) (Data := Data) (Native := Native) (IoError := IoError)
        (OsString := OsString) (Scope := Scope) resources encode granted
        ⟨c.frame.activation,[39]⟩ ⟨c.frame.activation,[45]⟩ cid s.next ch
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) := by
  intro cid ch _
  exact PV_OWN2_Exports.SourceInitBoxOwnership resources encode granted _ _ _ _ _ _

#print axioms callback_destination
#print axioms source_export
end PV_THR2_SourceOwnership
