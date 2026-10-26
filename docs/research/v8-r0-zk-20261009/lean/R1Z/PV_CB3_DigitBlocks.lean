import R1Z.PV_CB3_SamplerCarry
namespace R1Z.PV_CB3_DigitBlocks
open PV_CB3_SamplerCarry
set_option autoImplicit false

/-- Exact concatenation law for the source's little-endian loading order. -/
theorem value_append (base : Nat) (xs ys : List Nat) :
    value base (xs ++ ys) = value base xs + base ^ xs.length * value base ys := by
  induction xs with
  | nil => simp only [List.nil_append, value, List.length_nil, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | cons x xs ih =>
    simp only [List.cons_append, value, List.length_cons, ih, Nat.pow_succ, Nat.mul_add]
    ac_rfl

/-- Grouping fixed-width byte blocks preserves the whole input rank exactly. -/
theorem grouped_value (base width : Nat) (chunks : List (List Nat))
    (lengths : ∀ c, c ∈ chunks → c.length = width) :
    value (base ^ width) (chunks.map (value base)) = value base chunks.flatten := by
  induction chunks with
  | nil => rfl
  | cons c cs ih =>
    have hc := lengths c (List.mem_cons_self ..)
    have ht := ih (fun d h => lengths d (List.mem_cons_of_mem c h))
    simp only [List.map_cons, value, List.flatten_cons, value_append, hc, ht]

theorem grouped_canonical (base width : Nat) (chunks : List (List Nat))
    (lengths : ∀ c, c ∈ chunks → c.length = width)
    (canonical : ∀ c, c ∈ chunks → ∀ d, d ∈ c → d < base) :
    ∀ w, w ∈ chunks.map (value base) → w < base ^ width := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨c, hc, rfl⟩
  have h := value_lt_pow base c (canonical c hc)
  simpa only [lengths c hc] using h

#print axioms value_append
#print axioms grouped_value
#print axioms grouped_canonical
end R1Z.PV_CB3_DigitBlocks
