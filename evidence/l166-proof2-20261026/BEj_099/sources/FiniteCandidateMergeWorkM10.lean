import ExtractorListWorkM10
import FiniteListCandidateMerge

/-! The maintained merge's Cartesian extension, keep filter and dedup are
charged on their actual intermediate list lengths. Membership against the
deduplicated tail reserves the full tail comparison budget, including misses.
No bound of 100 is assumed for a pre-filter Cartesian intermediate. -/
set_option autoImplicit false
namespace AspisR1.FiniteCandidateMergeWorkM10
variable {X I M : Type} [Fintype I] [DecidableEq I] [DecidableEq M]

def dedup [DecidableEq X] (Ceq : Nat) : List X → List X × Nat
  | [] => ([],1)
  | x::xs =>
    let r := dedup Ceq xs
    (if x ∈ r.1 then r.1 else x::r.1,r.2+r.1.length*Ceq+3)

theorem dedup_value [DecidableEq X] (Ceq : Nat) (xs : List X) :
    (dedup Ceq xs).1 = xs.dedup := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [dedup, ih, List.dedup_cons']

theorem dedup_length [DecidableEq X] (Ceq : Nat) (xs : List X) :
    (dedup Ceq xs).1.length ≤ xs.length := by
  rw [dedup_value]
  exact (List.dedup_sublist xs).length_le

theorem dedup_work [DecidableEq X] (Ceq : Nat) (xs : List X) :
    (dedup Ceq xs).2 ≤ (xs.length+1)^2*(Ceq+3)+1 := by
  induction xs with
  | nil => simp [dedup]
  | cons x xs ih =>
    have hl := dedup_length Ceq xs
    have hm := Nat.mul_le_mul_right Ceq hl
    change _+_*Ceq+3 ≤ _
    simp only [List.length_cons]
    nlinarith [sq_nonneg (xs.length : Int)]

def advance (Ckeep Ceq : Nat) (keep : Finset I → (I → M) → Bool)
    (S : Finset I) (lane : I) (family : List (I → M)) (decoded : List M) :
    List (I → M) × Nat :=
  let raw := family.flatMap (fun t => decoded.map (Function.update t lane))
  let filtered := ExtractorListWorkM10.filter (fun t => (keep (insert lane S) t,Ckeep)) raw
  let out := dedup Ceq filtered.1
  (out.1,filtered.2+out.2+5*(family.length+1)*(decoded.length+1))

theorem advance_value (Ckeep Ceq : Nat) (keep : Finset I → (I → M) → Bool)
    (S : Finset I) (lane : I) (family : List (I → M)) (decoded : List M) :
    (advance Ckeep Ceq keep S lane family decoded).1 =
      FiniteListCandidateMerge.advance keep S lane family decoded := by
  simp only [advance, dedup_value, ExtractorListWorkM10.filter_value,
    FiniteListCandidateMerge.advance]

theorem raw_length (lane : I) (family : List (I → M)) (decoded : List M) :
    (family.flatMap (fun t => decoded.map (Function.update t lane))).length =
      family.length*decoded.length := by
  induction family with
  | nil => simp
  | cons t ts ih => simp only [List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.add_mul, Nat.one_mul, ih]; omega

theorem advance_length (Ckeep Ceq : Nat) (keep : Finset I → (I → M) → Bool)
    (S : Finset I) (lane : I) (family : List (I → M)) (decoded : List M) :
    (advance Ckeep Ceq keep S lane family decoded).1.length ≤ family.length*decoded.length := by
  have hd := dedup_length Ceq
    (ExtractorListWorkM10.filter (fun t => (keep (insert lane S) t,Ckeep))
      (family.flatMap (fun t => decoded.map (Function.update t lane)))).1
  have hf := ExtractorListWorkM10.filterMap_length
    (fun t => (if keep (insert lane S) t then some t else none,Ckeep))
    (family.flatMap (fun t => decoded.map (Function.update t lane)))
  exact hd.trans (hf.trans (raw_length lane family decoded).le)

def stageBudget (Ckeep Ceq F B : Nat) : Nat :=
  F*B*(Ckeep+2)+1+(F*B+1)^2*(Ceq+3)+1+5*(F+1)*(B+1)

theorem advance_work (Ckeep Ceq F B : Nat) (keep : Finset I → (I → M) → Bool)
    (S : Finset I) (lane : I) (family : List (I → M)) (decoded : List M)
    (hF : family.length ≤ F) (hB : decoded.length ≤ B) :
    (advance Ckeep Ceq keep S lane family decoded).2 ≤ stageBudget Ckeep Ceq F B := by
  let raw := family.flatMap (fun t => decoded.map (Function.update t lane))
  let filtered := ExtractorListWorkM10.filter (fun t => (keep (insert lane S) t,Ckeep)) raw
  have hf := ExtractorListWorkM10.filter_work (fun t => (keep (insert lane S) t,Ckeep)) raw
    Ckeep (fun _ _ => Nat.le_refl _)
  have hl := ExtractorListWorkM10.filterMap_length
    (fun t => (if keep (insert lane S) t then some t else none,Ckeep)) raw
  have hr : raw.length ≤ F*B := by
    rw [raw_length]
    exact Nat.mul_le_mul hF hB
  have hd := dedup_work Ceq filtered.1
  have hlen : filtered.1.length ≤ F*B := hl.trans hr
  have hsquare := Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) 2
  have hdedup := hd.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (Ceq+3) hsquare) 1)
  have hfilter := hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (Ckeep+2) hr) 1)
  have hcopy := Nat.mul_le_mul (Nat.mul_le_mul_left 5 (Nat.add_le_add_right hF 1))
    (Nat.add_le_add_right hB 1)
  have hc := Nat.add_le_add (Nat.add_le_add hfilter hdedup) hcopy
  simpa only [advance,stageBudget,raw,filtered,Nat.add_assoc] using hc

def run (Ckeep Ceq : Nat) (keep : Finset I → (I → M) → Bool)
    (decoded : I → List M) (S : Finset I) (family : List (I → M)) :
    List I → List (I → M) × Nat
  | [] => (family,1)
  | lane::rest =>
    let a := advance Ckeep Ceq keep S lane family (decoded lane)
    let b := run Ckeep Ceq keep decoded (insert lane S) a.1 rest
    (b.1,a.2+b.2+1)

theorem run_value (Ckeep Ceq : Nat) (keep : Finset I → (I → M) → Bool)
    (decoded : I → List M) (S : Finset I) (family : List (I → M)) (lanes : List I) :
    (run Ckeep Ceq keep decoded S family lanes).1 =
      FiniteListCandidateMerge.run keep decoded S family lanes := by
  induction lanes generalizing S family with
  | nil => rfl
  | cons lane rest ih => simp only [run, FiniteListCandidateMerge.run, ih, advance_value]

def budget (Ckeep Ceq B : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | n+1, F => stageBudget Ckeep Ceq F B+budget Ckeep Ceq B n (F*B)+1

theorem run_work (Ckeep Ceq B F : Nat) (keep : Finset I → (I → M) → Bool)
    (decoded : I → List M) (S : Finset I) (family : List (I → M)) (lanes : List I)
    (hF : family.length ≤ F) (hB : ∀ i, (decoded i).length ≤ B) :
    (run Ckeep Ceq keep decoded S family lanes).2 ≤ budget Ckeep Ceq B lanes.length F := by
  induction lanes generalizing S family F with
  | nil => exact Nat.le_refl _
  | cons lane rest ih =>
    have ha := advance_work Ckeep Ceq F B keep S lane family (decoded lane) hF (hB lane)
    have hl := (advance_length Ckeep Ceq keep S lane family (decoded lane)).trans
      (Nat.mul_le_mul hF (hB lane))
    have hb := ih (F*B) (insert lane S) (advance Ckeep Ceq keep S lane family (decoded lane)).1 hl
    exact Nat.add_le_add_right (Nat.add_le_add ha hb) 1

#print axioms dedup_value
#print axioms dedup_length
#print axioms dedup_work
#print axioms advance_value
#print axioms raw_length
#print axioms advance_length
#print axioms advance_work
#print axioms run_value
#print axioms run_work
end AspisR1.FiniteCandidateMergeWorkM10
