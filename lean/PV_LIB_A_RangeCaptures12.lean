import PV_LIB_A_RangeMatch12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeCaptures12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_PrefixMachine11 PV_LIB_A_RangeMatch12

/-- All eleven captures are source-selected storage/binds outside361. -/
theorem sites : PV_LIB_A_ChainTrace11.Sites PV_THR2_Source15LiveCaptures.chain := by
  change (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ (15 : Nat) ≠ 361 ∧ True
  decide

theorem break_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node19 :: PV_THR2_F15.block47.drop 8,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

/-- Certificate for every post-match outcome, including undefined discriminants
and failed captures. No successful field/read premise is introduced. -/
theorem trace (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program) (handler : PV_LIB_StoreActionTable.Handler)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Trace base ctl programs handler (PV_THR2_Source15LiveCaptures.steps base ctl s a w)
      (PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack) := by
  unfold PV_THR2_Source15LiveCaptures.steps PV_THR2_Source15LiveCaptures.tag
  cases hr : s.cells ⟨a,8,[]⟩ with
  | none => simp only [Option.bind_none]; trivial
  | some v =>
    simp only [Option.bind_some]
    cases hv : ctl.variant v with
    | none => trivial
    | some n =>
      cases n with
      | zero =>
        simp only
        have shape : PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack =
          ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node19 :: PV_THR2_F15.block47.drop 8,loops := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]},parents,write s ⟨a,9,[]⟩ none⟩,w,es⟩,stack⟩ := by
          simp [PV_THR2_Source15LoopMatch.after,PV_THR2_IntrinsicFrameMatch.result,PV_STX2_Store.read,write,hr,hv,selectVariant,PV_THR2_F15.block20]
        rw [shape]
        exact ⟨break_quiet programs _ a parents w es stack,True.intro⟩
      | succ n =>
        cases n with
        | zero =>
          simp only
          have shape : PV_THR2_Source15LoopMatch.after base ctl s a parents w es stack =
            ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.node23 :: PV_THR2_F15.node24 :: PV_THR2_F15.block47.drop 10,loops := [⟨PV_THR2_F15.block47,PV_THR2_F15.live.body.drop 13⟩]},parents,write s ⟨a,9,[]⟩ none⟩,w,es⟩,stack⟩ := by
            simp [PV_THR2_Source15LoopMatch.after,PV_THR2_IntrinsicFrameMatch.result,PV_STX2_Store.read,write,hr,hv,selectVariant]
            rfl
          rw [shape]
          change Trace base ctl programs handler
            (PV_THR2_IntrinsicFrameChain.steps base a w PV_THR2_Source15LiveCaptures.chain (write s ⟨a,9,[]⟩ none))
            ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 8,loops := loops},parents,write s ⟨a,9,[]⟩ none⟩,w,es⟩,stack⟩
          rw [← PV_THR2_Source15LiveCaptures.shape]
          exact PV_LIB_A_ChainTrace11.trace base ctl programs handler _ _ a parents loops _ w es stack sites
        | succ n => trivial

/-- Corrected-machine Some captures and None break. The same incoming iterator,
world, events, parent and suspended frames pass through the named provider run. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_LIB_StoreActionTable.Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    advance C K P resources encode H values (PV_THR2_Source15LiveCaptures.steps C K s a w)
      ⟨PV_THR2_Source15LoopMatch.after C K s a parents w es stack,none⟩ =
      ⟨PV_THR2_Source15LiveCaptures.after C K s a parents w es stack,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values _ _
    (trace C K P H s a parents w es stack)]
  exact congrArg (fun q => (⟨q,none⟩ : PV_LIB_StoreActionTable.SourceState))
    (PV_THR2_Source15LiveCaptures.run C K P H s a parents w es stack)

#print axioms sites
#print axioms break_quiet
#print axioms trace
#print axioms run
end PV_LIB_A_RangeCaptures12
