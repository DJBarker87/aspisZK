import AspisV8R19.PartialDot

/-! R62 ordered gather interface. The exact 181-term source inventory is
audited separately; this is not a Rust execution/refinement theorem. -/
set_option autoImplicit false
namespace AspisV8R19.CorrectionGather
variable {K : Type*} [AddMonoid K]

def scatterFrom (terms : List (Nat × K)) (out : Nat) (initial : K) : K :=
  match terms with
  | [] => initial
  | (i,v)::tail => scatterFrom tail out (if i=out then initial+v else initial)

def gather (terms : List (Nat × K)) (out : Nat) : K :=
  ((terms.filter (fun t => t.1=out)).map Prod.snd).sum

theorem scatterFrom_eq (terms : List (Nat × K)) (out : Nat) (initial : K) :
    scatterFrom terms out initial = initial + gather terms out := by
  induction terms generalizing initial with
  | nil => simp [scatterFrom,gather]
  | cons term tail ih =>
      rcases term with ⟨i,v⟩
      by_cases h : i=out
      · simp [scatterFrom,gather,h,ih,add_assoc]
      · simp [scatterFrom,gather,h,ih]

theorem scatter_eq_gather (terms : List (Nat × K)) (out : Nat) :
    scatterFrom terms out 0 = gather terms out := by
  simpa using scatterFrom_eq terms out 0

-- Apply the retained R59 residue theorem only after the same raw-product
-- sequence has been identified; no assumption on challenges or honest zeros.
theorem gathered_delayed_reduction (raw : List Nat) :
    (raw.map PartialProduct.foldOnce).sum % PartialProduct.p =
      raw.sum % PartialProduct.p := PartialDot.delayed_output_reduction raw

#print axioms scatterFrom_eq
#print axioms scatter_eq_gather
#print axioms gathered_delayed_reduction
end AspisV8R19.CorrectionGather
