import PV_LIB_SPEC_VectorKinds14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_PreludeValues14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_VectorKinds14

def fn164 : Data := match PV_THR2_F15.node4 with
  | .leaf (.call _ fn _ _ _) => fn | _ => .null
def fn165 : Data := match PV_THR2_F15.node8 with
  | .leaf (.call _ fn _ _ _) => fn | _ => .null
def fn93 : Data := match PV_THR2_F15.node17 with
  | .leaf (.call _ fn _ _ _) => fn | _ => .null
def raw : Data := PV_THR2_KeyValues.pack rawKind
  [PV_THR2_KeyValues.pack innerKind [.number 8,.number 0,.null],
   PV_THR2_KeyValues.pack markerKind []]
/-- Vec::new allocates nothing; empty cap0/len0 and dangling align8 pointer.
Exact3398 result type. Opaque Unique/cap use numeric source facets. -/
def vector : Data := PV_THR2_KeyValues.pack vectorKind [raw,.number 0]
def sizeKind (variant : Nat) : Data := match PV_LIB_SPEC_Builder269.sizeKind with
  | .object [("Adt",.array [ty,_,metadata])] => .object [("Adt",.array [ty,.number variant,metadata])]
  | _ => .null

def next (p : Parameters) (c : Config) (w : OWNER) (args : List Data) : Option Data := do
  let [reference] := args | none
  let (_,range) ← PV_THR2_SourceStoreLibrary.receiver (runtime p).carrier c.store w reference
  let .number start ← (runtime p).carrier.field range 0 | none
  let .number finish ← (runtime p).carrier.field range 1 | none
  if finish<2^64 ∧ start<2^64 then
    if start<finish then some (PV_THR2_KeyValues.pack (sizeKind 1) [.number start])
    else some (PV_THR2_KeyValues.pack (sizeKind 0) [])
  else none

/-- Only returned successes are interpreted here. Native93's SOURCE write
remains in unchanged v2; its returned Option is computed from the pre-store.
165 is the identity on the actual moved Range, not a supplied return marker. -/
def value (p : Parameters) (c : Config) (w : OWNER) (id : Nat)
    (args : List Data) : Option Data := match id,args with
  | 164,[] => some vector
  | 165,[range] => some range
  | 93,_ => next p c w args
  | _,_ => none

def reply (p : Parameters) (c : Config) (w : OWNER) (id : Nat) (args : List Data)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) :=
  match r.answer with
  | .returned (.ok _) => (value p c w id args).map (fun v => ⟨.returned (.ok v),w,[]⟩)
  | _ => some r

def rangeKind : Data := match PV_THR2_F15.node7 with
  | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null
def config (start finish : Nat) : Config :=
  ⟨{activation := 7,remaining := []},[],
    PV_STX2_Store.write PV_LIB_SPEC_Entry13.store ⟨7,7,[]⟩
      (some (PV_THR2_KeyValues.pack rangeKind [.number start,.number finish]))⟩
def arguments : List Data := [PV_STX2_TypedReferences.reference ⟨7,7,[]⟩ .null]

theorem range_next (p : Parameters) (w : OWNER) (start finish : Nat)
    (bs : start<2^64) (bf : finish<2^64) :
    next p (config start finish) w arguments =
      if start<finish then some (PV_THR2_KeyValues.pack (sizeKind 1) [.number start])
      else some (PV_THR2_KeyValues.pack (sizeKind 0) []) := by
  change (if finish<2^64 ∧ start<2^64 then _ else none) = _
  exact if_pos ⟨bf,bs⟩

theorem none_tag (p : Parameters) :
    (runtime p).control.variant (PV_THR2_KeyValues.pack (sizeKind 0) []) = some 0 := rfl

theorem some_tag (p : Parameters) (n : Nat) :
    (runtime p).control.variant (PV_THR2_KeyValues.pack (sizeKind 1) [.number n]) = some 1 ∧
    (runtime p).carrier.field (PV_THR2_KeyValues.pack (sizeKind 1) [.number n]) 0 = some (.number n) := ⟨rfl,rfl⟩

theorem other (p : Parameters) (c : Config) (w : OWNER) (id : Nat) (args : List Data)
    (r : Reply OWNER Event Data) (h : ∀ v, r.answer ≠ .returned (.ok v)) :
    reply p c w id args r = some r := by
  cases a : r.answer with
  | pending => simp only [reply,a]
  | fault f => simp only [reply,a]
  | returned out => cases out with
    | ok v => exact False.elim (h v a)
    | fail e => simp only [reply,a]
    | div => simp only [reply,a]

#print axioms fn164
#print axioms fn165
#print axioms fn93
#print axioms raw
#print axioms vector
#print axioms sizeKind
#print axioms next
#print axioms value
#print axioms reply
#print axioms rangeKind
#print axioms config
#print axioms arguments
#print axioms range_next
#print axioms none_tag
#print axioms some_tag
#print axioms other
end PV_LIB_SPEC_PreludeValues14
