import CurrentWideProduct
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.Proof

private theorem polynomial_step_bind_ok_inv {α β : Type}
    {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- One callback iteration of the extracted polynomial Horner fold.  The fold
    iterator and coefficient lookup remain external caller contracts. -/
theorem current_horner_step_success
    (acc multiplier coefficient out : field.wide_exact.WideExact)
    (hacc : CanonicalWide acc)
    (hmul : CanonicalWide multiplier)
    (hcoef : CanonicalWide coefficient)
    (hsuccess : (do
      let product ← field.wide_exact.WideExact.mul acc multiplier
      field.wide_exact.WideExact.add product coefficient) = .ok out) :
    CanonicalWide out ∧
      decodeWide out = decodeWide acc * decodeWide multiplier + decodeWide coefficient := by
  rcases polynomial_step_bind_ok_inv hsuccess with ⟨product, hproduct, hadd⟩
  have hp := wide_mul_success acc multiplier product hacc hmul hproduct
  have ha := wide_add_success product coefficient out hp.1 hcoef hadd
  refine ⟨ha.1, ?_⟩
  rw [ha.2, hp.2]

def current_horner_run (acc multiplier : field.wide_exact.WideExact) :
    List field.wide_exact.WideExact → Result field.wide_exact.WideExact
  | [] => .ok acc
  | coefficient :: rest => do
      let product ← field.wide_exact.WideExact.mul acc multiplier
      let next ← field.wide_exact.WideExact.add product coefficient
      current_horner_run next multiplier rest

def current_horner_lookup_run (acc multiplier : field.wide_exact.WideExact)
    (indices : List Nat) (lookup : Nat → Result field.wide_exact.WideExact) :
    Result field.wide_exact.WideExact :=
  match indices with
  | [] => .ok acc
  | index :: rest => do
      let product ← field.wide_exact.WideExact.mul acc multiplier
      let coefficient ← lookup index
      let next ← field.wide_exact.WideExact.add product coefficient
      current_horner_lookup_run next multiplier rest lookup

def horner_value (acc multiplier : AspisWideTower.WideExact)
    (coefficients : List AspisWideTower.WideExact) : AspisWideTower.WideExact :=
  coefficients.foldl (fun value coefficient => value * multiplier + coefficient) acc

def currentWideZero : field.wide_exact.WideExact :=
  ⟨⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩,
   ⟨⟨0#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩⟩

theorem currentWideZero_canonical : CanonicalWide currentWideZero := by
  norm_num [currentWideZero, CanonicalWide, CanonicalQM, toQM, toCM,
    AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
    AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
    AspisR1.ExtractedCurrentTowerAdd.P,
    AspisR1.ExtractedCurrentM31AddSub.P]

theorem currentWideZero_decodes_zero : decodeWide currentWideZero = 0 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> rfl
  · apply QuadraticAlgebra.ext <;> rfl

theorem current_horner_run_success
    (acc multiplier out : field.wide_exact.WideExact)
    (coefficients : List field.wide_exact.WideExact)
    (hacc : CanonicalWide acc)
    (hmultiplier : CanonicalWide multiplier)
    (hcoefficients : ∀ c ∈ coefficients, CanonicalWide c)
    (hrun : current_horner_run acc multiplier coefficients = .ok out) :
    CanonicalWide out ∧
      decodeWide out = horner_value (decodeWide acc) (decodeWide multiplier)
        (coefficients.map decodeWide) := by
  induction coefficients generalizing acc out with
  | nil =>
      simp [current_horner_run] at hrun
      subst out
      exact ⟨hacc, rfl⟩
  | cons coefficient rest ih =>
      have hcoef := hcoefficients coefficient (by simp)
      have htail : ∀ c ∈ rest, CanonicalWide c := by
        intro c hc
        exact hcoefficients c (by simp [hc])
      change (do
        let product ← field.wide_exact.WideExact.mul acc multiplier
        let next ← field.wide_exact.WideExact.add product coefficient
        current_horner_run next multiplier rest) = .ok out at hrun
      rcases polynomial_step_bind_ok_inv hrun with ⟨product, hproduct, hrun⟩
      rcases polynomial_step_bind_ok_inv hrun with ⟨next, hadd, hrun⟩
      have hstepRun : (do
          let product ← field.wide_exact.WideExact.mul acc multiplier
          field.wide_exact.WideExact.add product coefficient) = .ok next := by
        change Bind.bind (field.wide_exact.WideExact.mul acc multiplier)
          (fun product => field.wide_exact.WideExact.add product coefficient) = .ok next
        rw [hproduct]
        exact hadd
      have hstep : CanonicalWide next ∧
          decodeWide next = decodeWide acc * decodeWide multiplier + decodeWide coefficient :=
        current_horner_step_success acc multiplier coefficient next hacc hmultiplier hcoef
          hstepRun
      have hrest := ih next out hstep.1 htail hrun
      refine ⟨hrest.1, ?_⟩
      rw [hrest.2, hstep.2]
      simp [horner_value, List.map_cons, List.foldl_cons]

theorem current_horner_lookup_run_success_trace
    (acc multiplier out : field.wide_exact.WideExact)
    (indices : List Nat)
    (lookup : Nat → Result field.wide_exact.WideExact)
    (hacc : CanonicalWide acc)
    (hmultiplier : CanonicalWide multiplier)
    (hlookup : ∀ i c, lookup i = .ok c → CanonicalWide c)
    (hrun : current_horner_lookup_run acc multiplier indices lookup = .ok out) :
    ∃ coefficients, (∀ c ∈ coefficients, CanonicalWide c) ∧
      List.Forall₂ (fun i c => lookup i = .ok c) indices coefficients ∧
      current_horner_run acc multiplier coefficients = .ok out := by
  induction indices generalizing acc out with
  | nil =>
      simp [current_horner_lookup_run] at hrun
      subst out
      exact ⟨[], by simp, List.Forall₂.nil, by simp [current_horner_run]⟩
  | cons index rest ih =>
      change (do
        let product ← field.wide_exact.WideExact.mul acc multiplier
        let coefficient ← lookup index
        let next ← field.wide_exact.WideExact.add product coefficient
        current_horner_lookup_run next multiplier rest lookup) = .ok out at hrun
      rcases polynomial_step_bind_ok_inv hrun with ⟨product, hproduct, hrun⟩
      rcases polynomial_step_bind_ok_inv hrun with ⟨coefficient, hlookupSuccess, hrun⟩
      rcases polynomial_step_bind_ok_inv hrun with ⟨next, hadd, hrun⟩
      have hstepRun : (do
          let product ← field.wide_exact.WideExact.mul acc multiplier
          field.wide_exact.WideExact.add product coefficient) = .ok next := by
        change Bind.bind (field.wide_exact.WideExact.mul acc multiplier)
          (fun product => field.wide_exact.WideExact.add product coefficient) = .ok next
        rw [hproduct]
        exact hadd
      have hstep := current_horner_step_success acc multiplier coefficient next hacc
        hmultiplier (hlookup index coefficient hlookupSuccess) hstepRun
      have htail := ih next out hstep.1 hrun
      rcases htail with ⟨tail, htailCanonical, htailTrace, htailRun⟩
      refine ⟨coefficient :: tail, ?_, ?_, ?_⟩
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hlookup index c hlookupSuccess
        · exact htailCanonical c hc
      · exact List.Forall₂.cons hlookupSuccess htailTrace
      · change (do
          let product ← field.wide_exact.WideExact.mul acc multiplier
          let next ← field.wide_exact.WideExact.add product coefficient
          current_horner_run next multiplier tail) = .ok out
        simp only [hproduct, bind_tc_ok, hadd, bind_tc_ok, htailRun]

theorem current_horner_lookup7_success
    (multiplier out : field.wide_exact.WideExact)
    (lookup : Nat → Result field.wide_exact.WideExact)
    (hmultiplier : CanonicalWide multiplier)
    (hlookup : ∀ i c, lookup i = .ok c → CanonicalWide c)
    (hrun : current_horner_lookup_run currentWideZero multiplier
      [6,5,4,3,2,1,0] lookup = .ok out) :
    CanonicalWide out ∧ ∃ coefficients,
      (∀ c ∈ coefficients, CanonicalWide c) ∧
      List.Forall₂ (fun i c => lookup i = .ok c) [6,5,4,3,2,1,0] coefficients ∧
      current_horner_run currentWideZero multiplier coefficients = .ok out ∧
      decodeWide out = horner_value 0 (decodeWide multiplier)
        (coefficients.map decodeWide) := by
  obtain ⟨coefficients, hcoefficients, htrace, hlistRun⟩ :=
    current_horner_lookup_run_success_trace currentWideZero multiplier out
      [6,5,4,3,2,1,0] lookup currentWideZero_canonical hmultiplier hlookup hrun
  have hout := current_horner_run_success currentWideZero multiplier out
    coefficients currentWideZero_canonical hmultiplier hcoefficients hlistRun
  exact ⟨hout.1, coefficients, hcoefficients, htrace, hlistRun, by
    simpa only [currentWideZero_decodes_zero] using hout.2⟩

theorem current_horner7_success
    (multiplier c0 c1 c2 c3 c4 c5 c6 out : field.wide_exact.WideExact)
    (hmultiplier : CanonicalWide multiplier)
    (hc0 : CanonicalWide c0) (hc1 : CanonicalWide c1)
    (hc2 : CanonicalWide c2) (hc3 : CanonicalWide c3)
    (hc4 : CanonicalWide c4) (hc5 : CanonicalWide c5)
    (hc6 : CanonicalWide c6)
    (hrun : current_horner_run currentWideZero multiplier [c6,c5,c4,c3,c2,c1,c0] = .ok out) :
    CanonicalWide out ∧ decodeWide out =
      horner_value 0 (decodeWide multiplier)
        [decodeWide c6,decodeWide c5,decodeWide c4,decodeWide c3,
         decodeWide c2,decodeWide c1,decodeWide c0] := by
  have hcoeff : ∀ c ∈ [c6,c5,c4,c3,c2,c1,c0], CanonicalWide c := by
    intro c hc
    simp only [List.mem_cons, List.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    · exact hc6
    · exact hc5
    · exact hc4
    · exact hc3
    · exact hc2
    · exact hc1
    · exact hc0
    · simp at h
  have h := current_horner_run_success currentWideZero multiplier out
    [c6,c5,c4,c3,c2,c1,c0] currentWideZero_canonical hmultiplier hcoeff hrun
  refine ⟨h.1, ?_⟩
  simpa only [currentWideZero_decodes_zero, List.map_cons, List.map_nil] using h.2

#print axioms current_horner_step_success
#print axioms current_horner_run_success
#print axioms current_horner_lookup_run_success_trace
#print axioms current_horner_lookup7_success
#print axioms current_horner7_success
#print axioms currentWideZero_canonical
#print axioms currentWideZero_decodes_zero

end AspisR1CurrentWide.Proof
