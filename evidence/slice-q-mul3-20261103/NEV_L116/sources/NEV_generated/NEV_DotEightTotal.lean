import NEV_DotEight
import NEV_DotSweepStep
import NEV_DotInputs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NEV_DotEightTotal
open Aeneas Aeneas.Std Result AspisR1

theorem eight (n : Nat) (active : n<4) (coefficient : Array U32 8#usize)
    (canonical : ∀ word∈coefficient.val,word.val<NEG_DotDomain.P)
    (scalar : U32) (scalarCanonical : scalar.val<NEG_DotDomain.P)
    (sums : Array U64 8#usize) (invariant : NEV_DotSweep.Sweep n 0 sums) :
    ∃ out,NEV_DotEight.eight coefficient scalar sums=ok out ∧
      NEV_DotSweep.Sweep (n+1) 0 out := by
  obtain ⟨s1,h1,b1⟩:=NEV_DotSweepStep.step n active 0#usize (by decide)
    coefficient canonical scalar scalarCanonical sums invariant
  obtain ⟨s2,h2,b2⟩:=NEV_DotSweepStep.step n active 1#usize (by decide)
    coefficient canonical scalar scalarCanonical s1 b1
  obtain ⟨s3,h3,b3⟩:=NEV_DotSweepStep.step n active 2#usize (by decide)
    coefficient canonical scalar scalarCanonical s2 b2
  obtain ⟨s4,h4,b4⟩:=NEV_DotSweepStep.step n active 3#usize (by decide)
    coefficient canonical scalar scalarCanonical s3 b3
  obtain ⟨s5,h5,b5⟩:=NEV_DotSweepStep.step n active 4#usize (by decide)
    coefficient canonical scalar scalarCanonical s4 b4
  obtain ⟨s6,h6,b6⟩:=NEV_DotSweepStep.step n active 5#usize (by decide)
    coefficient canonical scalar scalarCanonical s5 b5
  obtain ⟨s7,h7,b7⟩:=NEV_DotSweepStep.step n active 6#usize (by decide)
    coefficient canonical scalar scalarCanonical s6 b6
  obtain ⟨s8,h8,b8⟩:=NEV_DotSweepStep.step n active 7#usize (by decide)
    coefficient canonical scalar scalarCanonical s7 b7
  refine ⟨s8,?_,NEV_DotSweepStep.next_term n s8 b8⟩
  simp only [NEV_DotEight.eight,h1,h2,h3,h4,h5,h6,h7,h8,bind_tc_ok]

theorem zero : NEV_DotSweep.Sweep 0 0 (Array.repeat 8#usize 0#u64) := by
  intro i
  change ((List.replicate 8 (0#u64))[i.val]'_).val≤
    (if i.val<0 then (0+1)*NEG_DotDomain.B else 0*NEG_DotDomain.B)
  simp only [List.getElem_replicate,Nat.not_lt_zero,if_false,Nat.zero_mul]
  exact Nat.le_refl 0

/-- SAME actual bounded g read, actual canonical projection and all eight
literal checked cells. No successful child or output is a caller premise. -/
theorem suffix (g : NEV_DotInputs.Coefficients) (canonical : NEV_DotInputs.Canonical g)
    (term : Usize) (inside : term.val<26) (scalar : U32) (scalarCanonical : scalar.val<NEG_DotDomain.P)
    (n : Nat) (active : n<4) (sums : Array U64 8#usize)
    (invariant : NEV_DotSweep.Sweep n 0 sums) :
    ∃ out,NEV_ActualDotStep.update g term scalar sums=ok out ∧
      NEV_DotSweep.Sweep (n+1) 0 out := by
  obtain ⟨value,read,_⟩:=WP.spec_imp_exists
    (Array.index_usize_spec g term (by change term.val<g.val.length;rw [g.property];change term.val<29;omega))
  have valueCanonical:=NEV_DotInputs.selected g canonical term (by omega) value read
  obtain ⟨words,projection,wordCanonical⟩:=NEV_DotInputs.limbs value valueCanonical
  obtain ⟨out,run,bound⟩:=eight n active words wordCanonical scalar scalarCanonical sums invariant
  refine ⟨out,?_,bound⟩
  rw [NEV_DotEight.suffix,read,bind_tc_ok,projection,bind_tc_ok,run]
#print axioms eight
#print axioms zero
#print axioms suffix
end NEV_DotEightTotal
end
