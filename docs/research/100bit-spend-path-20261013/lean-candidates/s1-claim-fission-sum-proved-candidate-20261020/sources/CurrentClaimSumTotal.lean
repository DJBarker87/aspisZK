import CurrentClaimSumSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim
open Concrete

def term (k parts : Array E 7#usize) (j : Nat) : AspisWideTower.WideExact :=
  if h : j<7 then
    decode (k.val[j]'(by rw [k.property]; exact h)) *
      decode (parts.val[j]'(by rw [parts.property]; exact h))
  else 0

def partialSum (k parts : Array E 7#usize) (n : Nat) : AspisWideTower.WideExact :=
  ∑ j ∈ Finset.range n, term k parts j

theorem sum_loop_total_exact (k parts : Array E 7#usize) (iter : Range) (claim : E)
    (hk : ∀ j h, Canonical (cell k j h)) (hp : ∀ j h, Canonical (cell parts j h))
    (hend : iter.end.val=7) (hi : iter.start.val≤7) (hc : Canonical claim)
    (he : decode claim=partialSum k parts iter.start.val) :
    ∃ out, verifier.prepared_claim_sum_loop iter k parts claim=.ok out ∧
      Canonical out ∧ decode out=partialSum k parts 7 := by
  have hw : WP.spec (verifier.prepared_claim_sum_loop iter k parts claim)
      (fun out => Canonical out ∧ decode out=partialSum k parts 7) := by
    unfold verifier.prepared_claim_sum_loop
    refine loop.spec_decr_nat
      (fun s : Range × E => 7-s.1.start.val)
      (fun s : Range × E => s.1.end.val=7 ∧ s.1.start.val≤7 ∧ Canonical s.2 ∧
        decode s.2=partialSum k parts s.1.start.val)
      (fun out => Canonical out ∧ decode out=partialSum k parts 7)
      (fun s : Range × E => verifier.prepared_claim_sum_loop.body k parts s.1 s.2)
      (iter,claim) ?_ ?_
    · intro s hs
      rcases s with ⟨r,c⟩
      rcases hs with ⟨hrend,hrle,hcc,hcp⟩
      change r.end.val=7 at hrend
      change r.start.val≤7 at hrle
      by_cases hlt : r.start.val<7
      · obtain ⟨r',c',hb,hstart,hend',hcanon,hdecode⟩ :=
          sum_body_step k parts r c hrend hlt (hk r.start hlt) (hp r.start hlt) hcc
        rw [hb,WP.spec_ok]
        change (r'.end.val=7 ∧ r'.start.val≤7 ∧ Canonical c' ∧
          decode c'=partialSum k parts r'.start.val) ∧ 7-r'.start.val<7-r.start.val
        constructor
        · refine ⟨by rw [hend']; exact hrend,by omega,hcanon,?_⟩
          rw [hdecode,hcp,hstart]
          simp only [partialSum,Finset.sum_range_succ]
          congr 1
          simp only [term,hlt,↓reduceDIte,cell]
        · omega
      · have heq : r.start.val=7 := by omega
        rw [sum_body_done k parts r c (by omega),WP.spec_ok]
        exact ⟨hcc,by simpa only [heq] using hcp⟩
    · exact ⟨hend,hi,hc,he⟩
  exact WP.spec_imp_exists hw

theorem zero_canonical : Canonical aspis_core.field.WideExact.ZERO := by
  norm_num [Canonical,toFull,toQM,toCM,aspis_core.field.WideExact.ZERO,aspis_core.field.QM31.ZERO,
    AspisR1CurrentWide.Proof.CanonicalWide,AspisR1CurrentWide.Proof.CanonicalQM,
    AspisR1CurrentWide.Proof.toQM,AspisR1CurrentWide.Proof.toCM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
    AspisR1.ExtractedCurrentTowerAdd.P,AspisR1.ExtractedCurrentM31AddSub.P]

theorem zero_decode : decode aspis_core.field.WideExact.ZERO=0 := by
  apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals apply QuadraticAlgebra.ext
  all_goals norm_num [decode,toFull,toQM,toCM,aspis_core.field.WideExact.ZERO,aspis_core.field.QM31.ZERO,
    AspisR1CurrentWide.Proof.decodeWide,AspisR1CurrentWide.Proof.decodeQM,
    AspisR1CurrentWide.Proof.toQM,AspisR1CurrentWide.Proof.toCM,
    AspisR1.ExtractedCurrentQM31Exact.decode]

theorem prepared_claim_sum_total_exact (k parts : Array E 7#usize)
    (hk : ∀ j h, Canonical (cell k j h)) (hp : ∀ j h, Canonical (cell parts j h)) :
    ∃ out, verifier.prepared_claim_sum k parts=.ok out ∧
      Canonical out ∧ decode out=partialSum k parts 7 := by
  obtain ⟨out,ho,hc,he⟩ := sum_loop_total_exact k parts
    {start:=0#usize,«end»:=7#usize} aspis_core.field.WideExact.ZERO hk hp
    (by scalar_tac) (by scalar_tac) zero_canonical (by simpa [partialSum] using zero_decode)
  refine ⟨out,?_,hc,he⟩
  simp only [verifier.prepared_claim_sum,ho,bind_tc_ok,trace.value]
#print axioms sum_loop_total_exact
#print axioms zero_canonical
#print axioms zero_decode
#print axioms prepared_claim_sum_total_exact
end AspisR1CurrentPreparedClaim
