import AspisR1CanonicalSampler.Funs
import CuSavingsLoopRelation
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalSampler
open Aeneas Aeneas.Std Result AspisR1CanonicalSampler
abbrev K := field.QM31
abbrev E := field.wide_exact.WideExact

def CanonicalK (q : K) : Prop :=
  q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647 ∧
  q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647
def Canonical (x : E) : Prop := CanonicalK x.c0 ∧ CanonicalK x.c1

theorem remainder_total (x : U32) : ∃ out : U32,
    (x % field.P : Result U32)=.ok out ∧ out.val<2147483647 := by
  have hp : field.P.val=2147483647 := by simp [field.P]
  obtain ⟨out,hr,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec x (y:=field.P) (by rw [hp];decide))
  refine ⟨out,hr,?_⟩
  rw [hv,hp]
  exact Nat.mod_lt _ (by decide)

theorem canonical_total (q : K) : ∃ out,
    field.wide_exact.canonical_qm31 q=.ok out ∧ CanonicalK out := by
  obtain ⟨a,ha,hac⟩ := remainder_total q.c0.a
  obtain ⟨b,hb,hbc⟩ := remainder_total q.c0.b
  obtain ⟨c,hc,hcc⟩ := remainder_total q.c1.a
  obtain ⟨d,hd,hdc⟩ := remainder_total q.c1.b
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,hac,hbc,hcc,hdc⟩
  simp only [field.wide_exact.canonical_qm31,
    field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    ha,hb,hc,hd,bind_tc_ok]

theorem new_total (left right : K) : ∃ out,
    field.wide_exact.WideExact.new left right=.ok out ∧ Canonical out := by
  obtain ⟨a,ha,hac⟩ := canonical_total left
  obtain ⟨b,hb,hbc⟩ := canonical_total right
  exact ⟨⟨a,b⟩,by simp only [field.wide_exact.WideExact.new,ha,hb,bind_tc_ok],hac,hbc⟩

theorem new_all (left right : K) :
    CuSavingsLoopRelation.All (field.wide_exact.WideExact.new left right) Canonical := by
  obtain ⟨out,hr,hc⟩ := new_total left right
  intro value hv
  cases Result.ok.inj (hr.symm.trans hv)
  exact hc

theorem decode8_all (words : Array U32 8#usize) :
    CuSavingsLoopRelation.All (sampler.decode8 words) Canonical := by
  unfold sampler.decode8
  repeat first
    | exact new_all _ _
    | apply CuSavingsLoopRelation.all_bind;intro

variable [Shared]

theorem ordinary_all (block : Array U8 32#usize) :
    CuSavingsLoopRelation.All (sampler.ordinary_sample block) Canonical := by
  unfold sampler.ordinary_sample
  apply CuSavingsLoopRelation.all_bind
  intro pair
  rcases pair with ⟨digits,quotient⟩
  exact decode8_all digits

theorem gamma_all (block : Array U8 32#usize) :
    CuSavingsLoopRelation.All (sampler.gamma_sample block) Canonical := by
  unfold sampler.gamma_sample
  apply CuSavingsLoopRelation.all_bind
  intro pair
  rcases pair with ⟨digits,quotient⟩
  apply CuSavingsLoopRelation.all_bind
  intro increment
  apply CuSavingsLoopRelation.all_bind
  intro pair
  rcases pair with ⟨wrapped,after⟩
  change CuSavingsLoopRelation.All (if wrapped then _ else sampler.decode8 after) Canonical
  split
  · apply CuSavingsLoopRelation.all_bind
    intro pair
    rcases pair with ⟨wrapped1,after1⟩
    exact decode8_all after1
  · exact decode8_all after

#print axioms remainder_total
#print axioms canonical_total
#print axioms new_total
#print axioms new_all
#print axioms decode8_all
#print axioms ordinary_all
#print axioms gamma_all
end AspisR1.CuSavingsCanonicalSampler
