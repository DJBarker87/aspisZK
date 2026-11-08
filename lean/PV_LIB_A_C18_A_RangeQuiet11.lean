import PV_LIB_A_C18_A_PrefixMachine11
import PV_LIB_A_C18_A_RangePoll11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeQuiet11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine
open PV_LIB_A_PrefixMachine11

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem main5 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 5,loops := []},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,by change ¬ ((15 : Nat) = 361 ∧ _); simp⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem main6 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 6,loops := []},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,by change ¬ ((15 : Nat) = 361 ∧ _); simp⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem main7 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 7,loops := []},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,True.intro⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem main8 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 8,loops := []},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,True.intro⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem main9 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 9,loops := []},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,by change ¬ ((15 : Nat) = 361 ∧ _); simp⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem main10 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 10,loops := []},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,by change ¬ ((15 : Nat) = 361 ∧ _); simp⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem main11 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 11,loops := []},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,True.intro⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem main12 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.live.body.drop 12,loops := []},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,True.intro⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem loop0 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 0,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,by change ¬ ((15 : Nat) = 361 ∧ _); simp⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem loop1 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 1,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,by change ¬ ((15 : Nat) = 361 ∧ _); simp⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem loop2 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 2,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,by change ¬ ((15 : Nat) = 361 ∧ _); simp⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem loop3 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 3,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,True.intro⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem loop4 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 4,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,True.intro⟩

/-- Only the emitted control shape is reduced; the symbolic store is untouched. -/
theorem loop5 (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F15.block47.drop 5,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc
    cases hc
    rfl
  · intro c hc
    cases hc
    exact ⟨rfl,rfl,True.intro⟩

#print axioms main5
#print axioms main6
#print axioms main7
#print axioms main8
#print axioms main9
#print axioms main10
#print axioms main11
#print axioms main12
#print axioms loop0
#print axioms loop1
#print axioms loop2
#print axioms loop3
#print axioms loop4
#print axioms loop5
end PV_LIB_A_RangeQuiet11
