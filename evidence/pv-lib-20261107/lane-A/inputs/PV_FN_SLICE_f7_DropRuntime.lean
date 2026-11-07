import PV_FN_SLICE_f7_DropContract
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_DropRuntime
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
/-- Provider and consumer use the identical COMPLETE effect store. The
footprint equivalence is proved, rather than inferred from matching names. -/
theorem effects_eq_w1 (x : PV_FN_SLICE_f7_Drop.Cut)
    (changes : Address → Option Data) :
    PV_FN_SLICE_f7_Drop.effects x changes =
      PV_W1_ArgumentEffects.finalStore (PV_FN_SLICE_ValueCarrier.carrier x.C)
        (PV_FN_SLICE_f7_Drop.w1Entry x) x.w changes := by
  classical
  change {x.s with cells := fun p =>
    if (PV_W5_DropLeaf.Writable (PV_FN_SLICE_ValueCarrier.carrier x.C)
      (PV_FN_SLICE_f7_Drop.entry x) x.w x.capture p) then changes p else x.s.cells p} =
    {x.s with cells := fun p =>
    if (PV_W1_ArgumentEffects.Writable (PV_FN_SLICE_ValueCarrier.carrier x.C)
      (PV_FN_SLICE_f7_Drop.w1Entry x) x.w p) then changes p else x.s.cells p}
  apply congrArg (fun (cells : Address → Option Data) => ({x.s with cells := cells} : Store Data))
  funext p
  rw [propext (PV_FN_SLICE_f7_Drop.writable_iff x p)]

/-- The source7 uniform resource handler reaches its FRAMED fallback at every
Drop request, in both registration phases. This is a symbolic request-shape
proof, with no assumed per-site handler equality and no resolver installation. -/
theorem drop (resources : PV_EVHB_OWNER.Resources) (encode : PV_EVHB_OWNER.Encode)
    {s : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_W5_NativeFrame.Backend) (fn capture : Data) (w : OWNER) :
    PV_STX2_Source7QUniformResourceHandler.handler resources encode entry external fallback
      (.drop fn capture) w =
    PV_STX2_Source7QUniformResourceHandler.lift fallback (.drop fn capture) w := by
  by_cases phase : w.next = s.next <;>
    simp only [PV_STX2_Source7QUniformResourceHandler.handler,
      PV_STX2_Source7QPreludeWorld.handler,phase,ite_true,ite_false,
      PV_STX2_Source7QUniformResourceHandler.ordinary,PV_STX2_Source7QAllocationReply.handler]

/-- The CLOSED W5 contract applies to the SAME reply produced by the named
uniform runtime at source178; it needs no native OWNER-WF hypothesis. This
binds the native handler layer, not the still-open source-Store transport. -/
theorem at_source178 (resources : PV_EVHB_OWNER.Resources) (encode : PV_EVHB_OWNER.Encode)
    {s : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_W5_NativeFrame.Backend) (x : PV_FN_SLICE_f7_Drop.Cut)
    (changes : Address → Option Data)
    (pre : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    PV_FN_SLICE_f7_Drop.Summary x fallback changes ∧
    PV_STX2_Source7QUniformResourceHandler.handler resources encode entry external fallback
      (.drop PV_FN_SLICE_f7_Drop.source x.capture) x.w = PV_FN_SLICE_f7_Drop.reply x fallback ∧
    PV_W1_OwnerWellFormed.OwnerWellFormed
      (PV_STX2_Source7QUniformResourceHandler.handler resources encode entry external fallback
        (.drop PV_FN_SLICE_f7_Drop.source x.capture) x.w).world
      (PV_FN_SLICE_f7_Drop.effects x changes).nextActivation := by
  have closed := PV_FN_SLICE_f7_Drop.contract x fallback changes pre
  have same := drop resources encode entry external fallback PV_FN_SLICE_f7_Drop.source x.capture x.w
  refine ⟨closed,same,?_⟩
  rw [same]
  exact closed.2.2.1
#print axioms effects_eq_w1
#print axioms drop
#print axioms at_source178
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print at_source178
end PV_FN_SLICE_f7_DropRuntime
