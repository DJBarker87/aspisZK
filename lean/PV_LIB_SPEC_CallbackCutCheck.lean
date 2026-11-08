import PV_LIB_SPEC_OwnInitComposition
set_option autoImplicit false
namespace PV_LIB_SPEC_CallbackCutCheck
open PV_STX2_Syntax PV_STX2_SliceSyntax
/-- Actual source13923 callback allocation is at source body index92. -/
theorem actual_allocation :
    PV_THR2_F361.live.body[92]? = some PV_THR2_F361.node125 := rfl
/-- AllocationWitness's retained drop94 starts at source14113, the
ManuallyDrop constructor CALL, after13923 and its storage-dead instruction. -/
theorem retained_cut :
    PV_THR2_F361.live.body[94]? = some PV_THR2_F361.node127 := rfl

def firstSite : List Node → Option Site
  | .leaf (.call site _ _ _ _) :: _ => some site
  | _ => none

theorem actual_site :
    (firstSite (PV_THR2_F361.live.body.drop 92)).map Site.statement = some 13923 := rfl

theorem retained_site :
    (firstSite (PV_THR2_F361.live.body.drop 94)).map Site.statement = some 14113 := rfl

theorem different_cuts :
    PV_THR2_F361.live.body.drop 94 ≠ PV_THR2_F361.live.body.drop 92 := by
  intro equal
  have sites := congrArg (fun ns => (firstSite ns).map Site.statement) equal
  change some (14113 : Nat) = some 13923 at sites
  cases sites

/-- The allocated backing is minted at the PRE-call counter. The cut94 store
has already consumed that activation, so it cannot name the same backing.
This directly rejects replaying13923 with cut94's store as AllocationWitness
currently does. It is a local source-association contradiction, not a proof
that all original-entry schedules or the full existential are impossible. -/
theorem backing_after_return (s : PV_STX2_Store.Store Data) (a dest : Nat)
    (payload value : Data) :
    PV_THR2_PacketBoxBacking.root
      (PV_THR2_StaticReply.returnedStore s a [payload] dest value) ≠
      PV_THR2_PacketBoxBacking.root s := by
  intro equal
  have counter := congrArg PV_STX2_Store.Address.activation equal
  change s.nextActivation+1 = s.nextActivation at counter
  omega

#print axioms backing_after_return

#print axioms actual_allocation
#print axioms retained_cut
#print axioms firstSite
#print axioms actual_site
#print axioms retained_site
#print axioms different_cuts
end PV_LIB_SPEC_CallbackCutCheck
