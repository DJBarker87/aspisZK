import PV_LIB_A_OwnerStore
import PV_LIB_A_Numbering
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WriterNumbering
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_STX2_LiveNumbering
/-- A source field update changes cells only. Undefined paths are retained;
this theorem neither assumes nor manufactures definedness at a caller. -/
theorem write_counter {W : Type} (C : Carrier W Data) (s t : Store Data)
    (p : Address) (value : Option Data) (defined : writeAddress C s p value = some t) :
    t.nextActivation = s.nextActivation := by
  cases fields : p.fields with
  | nil =>
    simp only [writeAddress,fields,Option.some.injEq] at defined
    subst t
    rfl
  | cons n rest =>
    simp only [writeAddress,fields] at defined
    change (s.cells {p with fields := []}).bind (fun root =>
      (replaceFields C (n :: rest) value root).bind (fun result =>
        some (write s {p with fields := []} (some result)))) = some t at defined
    cases cell : s.cells {p with fields := []} with
    | none => simp only [cell,Option.bind_none] at defined; cases defined
    | some root =>
      rw [cell] at defined
      change (replaceFields C (n :: rest) value root).bind (fun result =>
        some (write s {p with fields := []} (some result))) = some t at defined
      cases rebuilt : replaceFields C (n :: rest) value root with
      | none => rw [rebuilt] at defined; cases defined
      | some result =>
        rw [rebuilt] at defined
        have equal := Option.some.inj defined
        rw [← equal]
        rfl

/-- Numbering transfer for a local source-store operation. Only monotonicity
of the unused counter is needed. The existing slice push/stack/waiting lemmas
supply all numbering reasoning; no cross-callee counter equality is asserted. -/
theorem local_store (c : Config) (t : Store Data) (numbered : Numbered c)
    (counter : c.store.nextActivation ≤ t.nextActivation) :
    Numbered {c with store := t} :=
  ⟨Nat.lt_of_lt_of_le numbered.1 counter,
    waiting_mono numbered.2.1 counter,stack_mono numbered.2.2 counter⟩
#print axioms write_counter
#print axioms local_store
end PV_LIB_A_WriterNumbering
