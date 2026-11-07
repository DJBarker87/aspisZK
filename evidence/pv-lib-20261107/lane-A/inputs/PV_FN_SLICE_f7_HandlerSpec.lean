import PV_FN_SLICE_f7_DropRuntime
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_HandlerSpec
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
abbrev Handler := PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data
/-- Structural machine specification: bind the original handler to its named
runtime constructor, once. No success, post-world or per-call equality enters
this specification. The consumer still has to supply its actual runtime. -/
def Spec (H : Handler) : Prop :=
  ∃ (resources : PV_EVHB_OWNER.Resources) (encode : PV_EVHB_OWNER.Encode)
    (s : OWNER) (value : PV_STX2_Source7EntryOwned.Foundation)
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_W5_NativeFrame.Backend),
    H = PV_STX2_Source7QUniformResourceHandler.handler resources encode entry external fallback

/-- The named original runtime satisfies the specification by construction;
no installed replacement handler or resolver is used. -/
theorem original (resources : PV_EVHB_OWNER.Resources) (encode : PV_EVHB_OWNER.Encode)
    {s : OWNER} {value : PV_STX2_Source7EntryOwned.Foundation}
    (entry : PV_STX2_Source7EntryOwned.Source7EntryOwned s value)
    (external : Nat → PV_STX_World.World → Reply PV_STX_World.World PV_RJ4IDB.NativeEvent Unit)
    (fallback : PV_W5_NativeFrame.Backend) :
    Spec (PV_STX2_Source7QUniformResourceHandler.handler resources encode entry external fallback) :=
  ⟨resources,encode,s,value,entry,external,fallback,rfl⟩

/-- ONE backend agrees at every Drop site/world/value. This is derived from
request shape for the original handler, never assumed at the actual call. -/
theorem all_drops (H : Handler) (spec : Spec H) :
    ∃ fallback : PV_W5_NativeFrame.Backend, ∀ (fn capture : Data) (w : OWNER),
      H (.drop fn capture) w =
        PV_STX2_Source7QUniformResourceHandler.lift fallback (.drop fn capture) w := by
  obtain ⟨resources,encode,s,value,entry,external,fallback,rfl⟩ := spec
  exact ⟨fallback,PV_FN_SLICE_f7_DropRuntime.drop resources encode entry external fallback⟩

/-- The arbitrary original machine satisfying Spec uses the same CLOSED W5
summary on its full post-effect Store at178. No native OWNER-WF assumption. -/
theorem at_source178 (H : Handler) (spec : Spec H) (x : PV_FN_SLICE_f7_Drop.Cut)
    (changes : Address → Option Data)
    (pre : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    ∃ fallback : PV_W5_NativeFrame.Backend,
      PV_FN_SLICE_f7_Drop.Summary x fallback changes ∧
      H (.drop PV_FN_SLICE_f7_Drop.source x.capture) x.w = PV_FN_SLICE_f7_Drop.reply x fallback ∧
      PV_W1_OwnerWellFormed.OwnerWellFormed
        (H (.drop PV_FN_SLICE_f7_Drop.source x.capture) x.w).world
        (PV_FN_SLICE_f7_Drop.effects x changes).nextActivation := by
  obtain ⟨fallback,agree⟩ := all_drops H spec
  have closed := PV_FN_SLICE_f7_Drop.contract x fallback changes pre
  refine ⟨fallback,closed,agree _ _ _,?_⟩
  rw [agree]
  exact closed.2.2.1
#print axioms original
#print axioms all_drops
#print axioms at_source178
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print at_source178
end PV_FN_SLICE_f7_HandlerSpec
