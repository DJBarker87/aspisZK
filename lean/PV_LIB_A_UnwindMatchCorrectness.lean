import PV_LIB_A_UnwindMatch
set_option autoImplicit false
namespace PV_LIB_A_UnwindMatchCorrectness
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_A_UnwindMatch

def selectArm {α : Type} (n : Nat) : List (List Nat × List α) →
    Option (List α) → Option (List α)
  | [], other => other
  | (keys,body) :: rest, other => if n ∈ keys then some body else selectArm n rest other

theorem source_selector (n : Nat) (source : List (List Nat × List PV_STX2_SliceSyntax.Node))
    (other : Option (List PV_STX2_SliceSyntax.Node)) :
    selectVariant n source other = selectArm n source other := by
  induction source with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨keys,body⟩
    simp only [selectVariant,selectArm,ih]

theorem keys {W : Type} (C : Carrier W Data) (K : Control) (value : Data)
    (n : Nat) (known : K.variant value = some n) (source : List Nat) :
    (source.map variantKey).any ((carrier C K).matchesKey value) = decide (n ∈ source) := by
  induction source with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons,List.any_cons,variant_key,known,ih]
    by_cases h : n = head
    · subst head; simp
    · simp [h]

theorem variants {W : Type} (C : Carrier W Data) (K : Control) (value : Data)
    (n : Nat) (known : K.variant value = some n)
    (source : List (List Nat × List Instruction)) (other : List Instruction) :
    PV_STX2_Native.choose (carrier C K) value
      (source.map (fun (keys,body) => (keys.map variantKey,body))) other =
      (selectArm n source (some other)).getD other := by
  induction source with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨ks,body⟩
    simp only [List.map_cons,PV_STX2_Native.choose,keys C K value n known,selectArm]
    by_cases h : n ∈ ks
    · simp [h]
    · simp [h,ih]

/-- Exact arm selection on every value. Invalid source tags and unhandled
variants become interpretation gaps; no branch is converted to source abort. -/
theorem selection {W : Type} (C : Carrier W Data) (K : Control) (value : Data)
    (site : Site) (source : List (List Nat × List Instruction))
    (other : Option (List Instruction)) :
    PV_STX2_Native.choose (carrier C K) value (arms site source) (otherwise site other) =
      match K.variant value with
      | none => [gap site]
      | some n => (selectArm n source other).getD [gap site] := by
  cases known : K.variant value with
  | none => simp [arms,PV_STX2_Native.choose,invalid_key,known]
  | some n =>
    simp only [arms,PV_STX2_Native.choose,List.any_cons,List.any_nil,invalid_key,
      known,Option.isNone_some,Bool.false_or,Bool.false_eq_true,↓reduceIte]
    rw [variants C K value n known]
    induction source with
    | nil => cases other <;> rfl
    | cons head tail ih =>
      rcases head with ⟨ks,body⟩
      simp only [selectArm]
      split <;> simp_all

/-- The private gap operation is an undefined interpretation with unchanged
world and no event. It neither writes a temporary cell nor allocates memory. -/
theorem gap_is_undefined {W E : Type} (C : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (a : Nat) (s : Store Data) (w : W) (site : Site) :
    PV_STX2_Native.step (carrier C K) H ⟨a,[gap site],s,none,none⟩ w =
      ⟨.undefined (some site),w,[]⟩ := rfl

#print axioms selectArm
#print axioms source_selector
#print axioms keys
#print axioms variants
#print axioms selection
#print axioms gap_is_undefined
end PV_LIB_A_UnwindMatchCorrectness
