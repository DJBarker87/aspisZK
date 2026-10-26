import GSScalarTraceFieldWorkM10

/-! Actual occurrence lists, with their operands, populate Jobs. Raw power
jobs retain the same exponent/operands but are not identified with the GS
binaryRec work trace; the latter is bounded separately by general_work. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.GSScalarJobsM10
open CompPoly GSScalarCallScheduleM10 GSScalarOperandEnvelopeM10 RawExtractorCostLedger
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def ofCalls (D q : Nat) : (cs : List (Call K)) → (∀ c ∈ cs, Bounded D q c) → Jobs K
  | [], _ => ⟨[],[],[]⟩
  | c::cs, h =>
    let rest := ofCalls D q cs (fun c hc => h c (List.mem_cons_of_mem _ hc))
    match c with
    | .gcd a b => {rest with gcds := (a.val,b.val)::rest.gcds}
    | .power a m e => {rest with powers :=
        ⟨CPolynomial.Raw.MulContext.naive,CPolynomial.Raw.ModContext.naive,m.val,a.val,e⟩::rest.powers}
    | .division a b =>
      let hb := h (.division a b) List.mem_cons_self
      let hm := GSBinaryModPowerFieldWorkM10.monic_raw b hb.2.2
      {rest with divisions := ⟨a.val,b.val,
        CPolynomial.Raw.Trim.trim_eq_of_isCanonical a.property,
        hm.1,hm.2.1,hm.2.2⟩::rest.divisions}

theorem bounded (D q : Nat) (cs : List (Call K)) (h : ∀ c ∈ cs, Bounded D q c) :
    (ofCalls D q cs h).Bounded (D+1) (q+1) cs.length := by
  induction cs with
  | nil =>
    constructor <;> simp [ofCalls]
  | cons c cs ih =>
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have hh := h c List.mem_cons_self
    cases c with
    | gcd a b =>
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · simpa only [ofCalls, List.length_cons] using Nat.succ_le_succ ht.gcd_count
      · exact ht.division_count.trans (by simp)
      · exact ht.power_count.trans (by simp)
      · intro pq hpq
        rcases List.mem_cons.mp hpq with rfl | hpq
        · exact hh
        · exact ht.gcd_sizes pq hpq
      · exact ht.division_sizes
      · exact ht.power_bits
    | power a m e =>
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · exact ht.gcd_count.trans (by simp)
      · exact ht.division_count.trans (by simp)
      · simpa only [ofCalls, List.length_cons] using Nat.succ_le_succ ht.power_count
      · exact ht.gcd_sizes
      · exact ht.division_sizes
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact Nat.add_le_add_right ((Nat.log2_le_self e).trans hh.2.2.1) 1
        · exact ht.power_bits p hp
    | division a b =>
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · exact ht.gcd_count.trans (by simp)
      · simpa only [ofCalls, List.length_cons] using Nat.succ_le_succ ht.division_count
      · exact ht.power_count.trans (by simp)
      · exact ht.gcd_sizes
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hh.1
        · exact ht.division_sizes d hd
      · exact ht.power_bits

theorem general_jobs (p : CPolynomial K) (q t D : Nat)
    (H : Nat → Fin t → K × K) (hd : p.toPoly.natDegree ≤ D) (hD : 1 ≤ D) :
    ∃ jobs : Jobs K, jobs.Bounded (D+1) (q+1)
      (GSScalarSequentialScheduleM10.general p q t H).2.length := by
  have h := GSScalarRootEnvelopeM10.general_bounded p q t D H hd hD
  exact ⟨ofCalls D q _ h,bounded D q _ h⟩

#print axioms bounded
#print axioms general_jobs
end AspisR1.GSScalarJobsM10
end
