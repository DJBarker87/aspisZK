import NET_GeometryAllocation
import Port4C_BatchInverse
set_option autoImplicit false
namespace NEW_GeometryReverse
open Aeneas.Std
open AspisR1
open S7Kani2PrefixLoop (wordMul)
open Port4C_BatchInverse (cell)

/-- Pointwise native write observations identify the SAME output list, including
all unmodified cells. No independently selected whole-output equality is assumed. -/
theorem write_from_windows (before after : List U32) (index : Nat) (value : U32)
    (active : index < before.length) (size : after.length = before.length)
    (windows : ∀ j, j < before.length →
      after[j]? = if j = index then some value else before[j]?) :
    after = before.set index value := by
  apply List.ext_getElem?
  intro j
  by_cases h : j < before.length
  · rw [windows j h]
    by_cases same : j = index
    · subst j
      simp only [if_pos rfl,List.getElem?_set_self active]
    · simp only [same,if_false,List.getElem?_set_ne (Ne.symm same)]
  · have ha : after.length ≤ j := by omega
    have hb : (before.set index value).length ≤ j := by simpa only [List.length_set] using (show before.length ≤ j by omega)
    rw [List.getElem?_eq_none ha,List.getElem?_eq_none hb]

/-- One step uses two ordered products. Their replies have already been
instantiated by the existing emitted multiplication law; no arithmetic Kani. -/
inductive Trace (flat prefixes : List U32) :
    Nat → List U32 → U32 → List U32 → U32 → List (U32 × U32) → Prop
 | done (inverse : List U32) (suffix : U32) :
     Trace flat prefixes 0 inverse suffix inverse suffix []
 | step (n : Nat) (inverse next final : List U32) (suffix finalSuffix : U32)
     (tailCalls : List (U32 × U32))
     (active : n < inverse.length)
     (size : next.length = inverse.length)
     (windows : ∀ j, j < inverse.length → next[j]? =
       if j = n then some (wordMul suffix (cell prefixes n)) else inverse[j]?)
     (tail : Trace flat prefixes n next (wordMul suffix (cell flat n)) final finalSuffix tailCalls) :
     Trace flat prefixes (n+1) inverse suffix final finalSuffix
       ((suffix,cell prefixes n)::(suffix,cell flat n)::tailCalls)

def suffixAfter (flat : List U32) : Nat → U32 → U32
 | 0,suffix => suffix
 | n+1,suffix => suffixAfter flat n (wordMul suffix (cell flat n))

/-- The exact mutable output AND returned suffix compose by reverse induction.
This consumes every frame observation, not just the newly written cell. -/
theorem state (flat prefixes : List U32) {n : Nat} {inverse final : List U32}
    {suffix finalSuffix : U32} {calls : List (U32 × U32)}
    (trace : Trace flat prefixes n inverse suffix final finalSuffix calls) :
    final = Port4C_OwnedInverse.model flat prefixes n inverse suffix ∧
      finalSuffix = suffixAfter flat n suffix := by
  induction trace with
  | done => exact ⟨rfl,rfl⟩
  | step n inverse next final suffix finalSuffix calls active size windows tail ih =>
    have same := write_from_windows inverse next n (wordMul suffix (cell prefixes n)) active size windows
    rcases ih with ⟨output,returned⟩
    constructor
    · rw [output,same]
      rfl
    · exact returned

/-- The two calls in each native cell precede all calls for lower cells. -/
theorem call_count (flat prefixes : List U32) {n : Nat} {inverse final : List U32}
    {suffix finalSuffix : U32} {calls : List (U32 × U32)}
    (trace : Trace flat prefixes n inverse suffix final finalSuffix calls) :
    calls.length = 2*n := by
  induction trace with
  | done => rfl
  | step n inverse next final suffix finalSuffix calls active size windows tail ih =>
    simp only [List.length_cons]
    omega

#print axioms write_from_windows
#print axioms state
#print axioms call_count
end NEW_GeometryReverse
