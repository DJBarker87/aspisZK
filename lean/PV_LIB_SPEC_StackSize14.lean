import PV_LIB_SPEC_PrefixNative13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_StackSize14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ThreadWords12
local instance : DecidableEq Data := Classical.decEq _
/-- Adopted ELF fc8808eb, relocation1b3740 ->1b67c0; e0487/e048f
loads the cached MIN, subtracting one. Cold env/string parsing remains a gap. -/
def minimumOffset : Nat := 0x1b67c0
def closureKind : Data := match PV_THR2_F361.node22 with
  | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null
def token : Data := match PV_THR2_F361.node23 with
  | .leaf (.call _ fn _ _ _) => fn | _ => .null

def value (p : Parameters) (w : OWNER) (args : List Data) : Option Data := do
  let [size,closure] := args | none
  if closure ≠ PV_THR2_KeyValues.pack closureKind [] then none else do
    match (runtime p).control.variant size with
    | some 1 => do
      let .number n ← (runtime p).carrier.field size 0 | none
      if n < 2^64 then some (.number n) else none
    | some 0 => do
      let cached ← read w (p.loadBias.val+minimumOffset)
      if cached.val=0 then none else some (.number (cached.val-1))
    | _ => none

def reply (p : Parameters) (w : OWNER) (args : List Data)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) :=
  match r.answer with
  | .returned (.ok _) => (value p w args).map (fun v => ⟨.returned (.ok v),w,r.events⟩)
  | _ => some r

theorem cached (p : Parameters) (w : OWNER) (n : Pointer) (nonzero : n.val ≠ 0) :
    value p (write w (p.loadBias.val+minimumOffset) n.val)
      [PV_THR2_KeyValues.pack PV_LIB_SPEC_Builder269.sizeKind [],
       PV_THR2_KeyValues.pack closureKind []] = some (.number (n.val-1)) := by
  unfold value
  simp only [ne_eq,not_true_eq_false,ite_false]
  change (do let cached ← read (write w (p.loadBias.val+minimumOffset) n.val)
                (p.loadBias.val+minimumOffset)
             if cached.val=0 then none else some (Data.number (cached.val-1))) = _
  rw [read_written]
  exact if_neg nonzero

theorem other (p : Parameters) (w : OWNER) (args : List Data)
    (r : Reply OWNER Event Data) (h : ∀ v, r.answer ≠ .returned (.ok v)) :
    reply p w args r = some r := by
  cases a : r.answer with
  | pending => simp only [reply,a]
  | fault f => simp only [reply,a]
  | returned result => cases result with
    | ok v => exact False.elim (h v a)
    | fail e => simp only [reply,a]
    | div => simp only [reply,a]

#print axioms minimumOffset
#print axioms closureKind
#print axioms token
#print axioms value
#print axioms reply
#print axioms cached
#print axioms other
end PV_LIB_SPEC_StackSize14
