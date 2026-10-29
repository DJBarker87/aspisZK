import R1Z.PV_OWNL_HelperSlots
set_option autoImplicit false
namespace R1Z.PV_OWNL_HelperRows
open PV_OWNK_TowerCanon PV_OWNL_HelperSlots
structure Row where
 producers : List Slot
 consumers : List Slot

def row (inverse : Q → Option Q) (chi : Q) (r : Row) : Option Q := do
 let p ← slots inverse chi true r.producers zero
 slots inverse chi false r.consumers p

theorem row_canonical (inverse : Q → Option Q) (chi out : Q) (r : Row)
 (h : row inverse chi r = some out) : Canon out := by
 unfold row at h
 cases hs : slots inverse chi true r.producers zero with
 | none => simp only [hs,Option.bind_none] at h; cases h
 | some p =>
  simp only [hs,Option.bind_some] at h
  exact slots_canonical inverse chi false r.consumers p out
   (slots_canonical inverse chi true r.producers zero p zero_canon hs) h

/-- Direct helper[r] store; preserves canonical initialized and spare slots. -/
theorem store_canonical (helper : List Q) (index : Nat) (value : Q)
 (hh : ∀ q ∈ helper, Canon q) (hv : Canon value) :
 ∀ q ∈ helper.set index value, Canon q := by
 intro q hq
 have h := List.mem_or_eq_of_mem_set hq
 rcases h with h | h
 · exact hh q h
 · exact h ▸ hv

/-- Source row loop, retaining its successful stores and early failure. -/
def rows (inverse : Q → Option Q) (chi : Q) : List Row → Nat → List Q → Option (List Q)
 | [],_,helper => some helper
 | r::rs,index,helper => do
  let value ← row inverse chi r
  rows inverse chi rs (index+1) (helper.set index value)

theorem rows_canonical (inverse : Q → Option Q) (chi : Q) (rs : List Row)
 (index : Nat) (helper out : List Q) (hh : ∀ q ∈ helper, Canon q)
 (h : rows inverse chi rs index helper = some out) : ∀ q ∈ out, Canon q := by
 induction rs generalizing index helper with
 | nil => exact Option.some.inj h ▸ hh
 | cons r rs ih =>
  simp only [rows] at h
  cases hr : row inverse chi r with
  | none => simp only [hr,Option.bind_none] at h; cases h
  | some value =>
   simp only [hr,Option.bind_some] at h
   exact ih _ _ (store_canonical helper index value hh
    (row_canonical inverse chi value r hr)) h

theorem helper_canonical (inverse : Q → Option Q) (chi : Q) (rs : List Row)
 (out : List Q) (h : rows inverse chi rs 0 (List.replicate 1024 zero) = some out) :
 ∀ q ∈ out, Canon q := by
 apply rows_canonical inverse chi rs 0 _ out _ h
 intro q hq
 have hzero := List.eq_of_mem_replicate hq
 exact hzero ▸ zero_canon
#print axioms row_canonical
#print axioms store_canonical
#print axioms rows_canonical
#print axioms helper_canonical
end R1Z.PV_OWNL_HelperRows
