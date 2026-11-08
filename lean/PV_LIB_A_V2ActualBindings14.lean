import PV_LIB_A_V2PrefixTables14
import PV_LIB_A_V2NativeFrontier14
set_option autoImplicit false
noncomputable section
/- Each call requires only its exact emitted lookup. In particular all uses
except native124 remain compatible with lane C's Full.programs. Native124 is
retained support for old tables ONLY: Full.programs executes BODY124. -/
namespace PV_LIB_A_V2ActualBindings14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_PrefixMachine11 PV_LIB_A_StructuredFrontier13 PV_LIB_A_V2PrefixTables14

abbrev src121 := PV_LIB_A_PrefixNativeCalls14.src121
abbrev rest121 := PV_LIB_A_PrefixNativeCalls14.rest121
abbrev steps121 := PV_LIB_A_PrefixNativeCalls14.steps121
abbrev after121 := PV_LIB_A_PrefixNativeCalls14.after121
theorem run121 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src121) = none) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps121 C q) q = after121 C H q := by
  apply PV_LIB_A_V2NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match P (fn src121) with | some _ => none | none => (v2Source (fn src121)).bind _) = none
      rw [lookup]
      rfl
    · intro c hc; cases hc
      cases vs with
      | nil => exact ⟨rfl,rfl,True.intro⟩
      | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · exact lookup

#print axioms run121

abbrev src122 := PV_LIB_A_PrefixNativeCalls14.src122
abbrev rest122 := PV_LIB_A_PrefixNativeCalls14.rest122
abbrev steps122 := PV_LIB_A_PrefixNativeCalls14.steps122
abbrev after122 := PV_LIB_A_PrefixNativeCalls14.after122
theorem run122 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src122) = none) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps122 C q) q = after122 C H q := by
  apply PV_LIB_A_V2NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match P (fn src122) with | some _ => none | none => (v2Source (fn src122)).bind _) = none
      rw [lookup]
      rfl
    · intro c hc; cases hc
      cases vs with
      | nil => exact ⟨rfl,rfl,True.intro⟩
      | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · exact lookup

#print axioms run122

abbrev src123 := PV_LIB_A_PrefixNativeCalls14.src123
abbrev rest123 := PV_LIB_A_PrefixNativeCalls14.rest123
abbrev steps123 := PV_LIB_A_PrefixNativeCalls14.steps123
abbrev after123 := PV_LIB_A_PrefixNativeCalls14.after123
theorem run123 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src123) = none) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps123 C q) q = after123 C H q := by
  apply PV_LIB_A_V2NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match P (fn src123) with | some _ => none | none => (v2Source (fn src123)).bind _) = none
      rw [lookup]
      rfl
    · intro c hc; cases hc
      cases vs with
      | nil => exact ⟨rfl,rfl,True.intro⟩
      | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · exact lookup

#print axioms run123

abbrev src124 := PV_LIB_A_PrefixNativeCalls14.src124
abbrev rest124 := PV_LIB_A_PrefixNativeCalls14.rest124
abbrev steps124 := PV_LIB_A_PrefixNativeCalls14.steps124
abbrev after124 := PV_LIB_A_PrefixNativeCalls14.after124
theorem run124 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src124) = none) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps124 C q) q = after124 C H q := by
  apply PV_LIB_A_V2NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match P (fn src124) with | some _ => none | none => (v2Source (fn src124)).bind _) = none
      rw [lookup]
      rfl
    · intro c hc; cases hc
      cases vs with
      | nil => exact ⟨rfl,rfl,True.intro⟩
      | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · exact lookup

#print axioms run124

abbrev src134 := PV_LIB_A_PrefixNativeCalls14.src134
abbrev rest134 := PV_LIB_A_PrefixNativeCalls14.rest134
abbrev steps134 := PV_LIB_A_PrefixNativeCalls14.steps134
abbrev after134 := PV_LIB_A_PrefixNativeCalls14.after134
theorem run134 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src134) = none) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps134 C q) q = after134 C H q := by
  apply PV_LIB_A_V2NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match P (fn src134) with | some _ => none | none => (v2Source (fn src134)).bind _) = none
      rw [lookup]
      rfl
    · intro c hc; cases hc
      cases vs with
      | nil => exact ⟨rfl,rfl,True.intro⟩
      | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · exact lookup

#print axioms run134

abbrev src410 := PV_LIB_A_PrefixNativeCalls14.src410
abbrev rest410 := PV_LIB_A_PrefixNativeCalls14.rest410
abbrev steps410 := PV_LIB_A_PrefixNativeCalls14.steps410
abbrev after410 := PV_LIB_A_PrefixNativeCalls14.after410
theorem run410 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src410) = none) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps410 C q) q = after410 C H q := by
  apply PV_LIB_A_V2NativeFrontier14.run
  · decide
  · intro s a w; rfl
  · intro t a parents loops vs w es stack
    constructor
    · intro c hc; cases hc
      unfold sourceSelect
      change (match P (fn src410) with | some _ => none | none => (v2Source (fn src410)).bind _) = none
      rw [lookup]
      rfl
    · intro c hc; cases hc
      cases vs with
      | nil => exact ⟨rfl,rfl,True.intro⟩
      | cons v vs => cases vs <;> exact ⟨rfl,rfl,True.intro⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · exact lookup

#print axioms run410

abbrev src125 := PV_LIB_A_PrefixStructuredCalls14.src125
abbrev rest125 := PV_LIB_A_PrefixStructuredCalls14.rest125
abbrev steps125 := PV_LIB_A_PrefixStructuredCalls14.steps125
abbrev after125 := PV_LIB_A_PrefixStructuredCalls14.after125
theorem run125 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src125) = some PV_THR2_F125.live) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps125 C q) q = after125 C q := by
  apply PV_LIB_A_V2Frontiers14.structured
  · decide
  · intro t a parents loops vs
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · intro s a w; rfl
  · exact lookup

#print axioms run125

abbrev src219 := PV_LIB_A_PrefixStructuredCalls14.src219
abbrev rest219 := PV_LIB_A_PrefixStructuredCalls14.rest219
abbrev steps219 := PV_LIB_A_PrefixStructuredCalls14.steps219
abbrev after219 := PV_LIB_A_PrefixStructuredCalls14.after219
theorem run219 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src219) = some PV_THR2_F219.live) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps219 C q) q = after219 C q := by
  apply PV_LIB_A_V2Frontiers14.structured
  · decide
  · intro t a parents loops vs
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · intro s a w; rfl
  · exact lookup

#print axioms run219

abbrev src220 := PV_LIB_A_PrefixStructuredCalls14.src220
abbrev rest220 := PV_LIB_A_PrefixStructuredCalls14.rest220
abbrev steps220 := PV_LIB_A_PrefixStructuredCalls14.steps220
abbrev after220 := PV_LIB_A_PrefixStructuredCalls14.after220
theorem run220 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src220) = some PV_THR2_F220.live) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps220 C q) q = after220 C q := by
  apply PV_LIB_A_V2Frontiers14.structured
  · decide
  · intro t a parents loops vs
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · intro s a w; rfl
  · exact lookup

#print axioms run220

abbrev src208 := PV_LIB_A_PrefixStructuredCalls14.src208
abbrev rest208 := PV_LIB_A_PrefixStructuredCalls14.rest208
abbrev steps208 := PV_LIB_A_PrefixStructuredCalls14.steps208
abbrev after208 := PV_LIB_A_PrefixStructuredCalls14.after208
theorem run208 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src208) = some PV_THR2_F208.live) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps208 C q) q = after208 C q := by
  apply PV_LIB_A_V2Frontiers14.structured
  · decide
  · intro t a parents loops vs
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · intro s a w; rfl
  · exact lookup

#print axioms run208

abbrev src15 := PV_LIB_A_PrefixStructuredCalls14.src15
abbrev rest15 := PV_LIB_A_PrefixStructuredCalls14.rest15
abbrev steps15 := PV_LIB_A_PrefixStructuredCalls14.steps15
abbrev after15 := PV_LIB_A_PrefixStructuredCalls14.after15
theorem run15 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookup : P (fn src15) = some PV_THR2_F15.live) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (steps15 C q) q = after15 C q := by
  apply PV_LIB_A_V2Frontiers14.structured
  · decide
  · intro t a parents loops vs
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons v vs => cases vs <;> exact ⟨rfl,rfl⟩
  · intro t a parents loops vs
    apply PV_THR2_IntrinsicFrameOrdinary.run
    intro eq
    have bad := congrArg PV_THR2_OffPath.functionId eq
    cases bad
  · intro s a w; rfl
  · exact lookup

#print axioms run15
end PV_LIB_A_V2ActualBindings14
