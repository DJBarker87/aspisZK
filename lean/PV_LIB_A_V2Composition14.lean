import PV_LIB_A_V2Frontiers14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2Composition14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11

/-- Deterministic proof-local segment evaluators. No native law, state write or
callee reply is a field; actual uses name the proved source segments. -/
structure Segment where
  steps : State → Nat
  after : State → State

def join (x y : Segment) : Segment :=
  ⟨fun q => x.steps q + y.steps (x.after q),fun q => y.after (x.after q)⟩
def chain : List Segment → Segment
  | [] => ⟨fun _ => 0,id⟩
  | x :: xs => join x (chain xs)

def Certified (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (x : Segment) : Prop :=
  ∀ q, PV_LIB_StoreActionTable.advance C K P resources encode H values (x.steps q) q = x.after q

theorem advance_add (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n m : Nat) (q : State) :
    PV_LIB_StoreActionTable.advance C K P resources encode H values (n+m) q =
      PV_LIB_StoreActionTable.advance C K P resources encode H values m
        (PV_LIB_StoreActionTable.advance C K P resources encode H values n q) := by
  induction n generalizing q with
  | zero => simp only [Nat.zero_add,PV_LIB_StoreActionTable.advance]
  | succ n ih =>
    simpa only [Nat.succ_add,PV_LIB_StoreActionTable.advance] using
      ih (PV_LIB_StoreActionTable.step C K P resources encode H values q)

/-- Composition uses the actual preceding store/world/events and phase. The
counter is never equated with a callee summary counter. -/
theorem joined (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (x y : Segment)
    (first : Certified C K P resources encode H values x)
    (second : Certified C K P resources encode H values y) :
    Certified C K P resources encode H values (join x y) := by
  intro q
  change PV_LIB_StoreActionTable.advance C K P resources encode H values (x.steps q+y.steps (x.after q)) q = _
  rw [advance_add,first q,second]
  rfl

theorem chained (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (xs : List Segment)
    (certificates : ∀ x ∈ xs, Certified C K P resources encode H values x) :
    Certified C K P resources encode H values (chain xs) := by
  induction xs with
  | nil => intro q; rfl
  | cons x xs ih =>
    exact joined C K P resources encode H values x (chain xs)
      (certificates x (by simp)) (ih (fun y hy => certificates y (by simp [hy])))

#print axioms advance_add
#print axioms join
#print axioms chain
#print axioms advance_add
#print axioms joined
#print axioms chained
end PV_LIB_A_V2Composition14
