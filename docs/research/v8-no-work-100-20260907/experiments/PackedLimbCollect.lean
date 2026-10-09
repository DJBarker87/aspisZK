import CanonicalCollect

/-! Canonical packed integers: success determines the actual integer, not
just the bound carried by the result type. Generic in count and modulus. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 10000
namespace AspisV8.PackedLimbCollect

def decode (p raw : Nat) : Option (Fin p) :=
  if h : raw < p then some ⟨raw,h⟩ else none

theorem decode_success {p raw : Nat} (value : Fin p)
    (success : decode p raw = some value) :
    raw = value.val := by
  unfold decode at success
  split at success
  · exact congrArg Fin.val (Option.some.inj success)
  · contradiction

theorem decode_reject {p raw : Nat} (high : p ≤ raw) :
    decode p raw = none := by
  simp only [decode,dif_neg (not_lt_of_ge high)]

def collect {n : Nat} (p : Nat) (raw : Fin n → Nat) : Option (List (Fin p)) :=
  CanonicalCollect.collect (decode p) (List.ofFn raw)

theorem success_raw {n p : Nat} (raw : Fin n → Nat)
    (values : List (Fin p)) (default : Fin p)
    (success : collect p raw = some values) :
    values.length = n ∧ ∀ i : Fin n,
      raw i = (values.getD i.val default).val := by
  obtain ⟨length,entries⟩ := CanonicalCollect.success_ofFn (decode p)
    raw values default success
  exact ⟨length,fun i=>decode_success _ (entries i)⟩

theorem rejects_any {n p : Nat} (raw : Fin n → Nat) (default : Fin p)
    (i : Fin n) (high : p ≤ raw i) : collect p raw = none := by
  cases result : collect p raw with
  | none => rfl
  | some values =>
    have exactValue := (success_raw raw values default result).2 i
    have bound := (values.getD i.val default).isLt
    rw [←exactValue] at bound
    exact False.elim ((not_lt_of_ge high) bound)

#print axioms decode_success
#print axioms decode_reject
#print axioms success_raw
#print axioms rejects_any
end AspisV8.PackedLimbCollect
