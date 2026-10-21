import S4HeadReadForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsHeadTermForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops M31)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide TermBody ReadWitness term_body_from_reads)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (Range cap cell)

theorem term_body_forward
    (ops : Ops) (k : Nat) (hk : k≤3)
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (iter iter' : Range) (sums : Array Std.U64 8#usize)
    (r : ReadWitness a g slot term) (scalar : M31) (coefficient : Array Std.U32 8#usize)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some term,iter'))
    (hp : ops.m31FromBytes r.copied = .ok (some scalar))
    (hw : ops.wideToLimbs r.coefficient = .ok coefficient)
    (hc : ops.wideLimbCount = .ok 8#usize)
    (hcoeff : ∀ j : Fin 8,
      (coefficient.val[j.val]'(by simpa [coefficient.property] using j.isLt)).val < 2147483647)
    (hscalar : scalar.val<2147483647)
    (hinput : ∀ j : Fin 8, cell sums j ≤ k*cap) :
    ∃ out : Array Std.U64 8#usize,
      TermBody ops a g slot iter sums = .ok (.cont (iter',out)) ∧
      (∀ j : Fin 8, cell out j ≤ (k+1)*cap) := by
  have hbase : ∀ j : Fin 8, cell sums j ≤ (k+1)*cap := by
    intro j
    exact le_trans (hinput j) (Nat.mul_le_mul_right cap (Nat.le_succ k))
  obtain ⟨out,hl,hbound⟩ := AspisR1FastDotsHeadLoopForwardRootV1.inner_loop_forward
    ops k hk coefficient 0#usize sums scalar (by decide) hcoeff hbase
    (by intro j _; exact hinput j) hscalar
  exact ⟨out,term_body_from_reads ops a g slot term iter iter' sums out r scalar coefficient
    hn hp hw hc hl,hbound⟩

#print axioms term_body_forward
end AspisR1FastDotsHeadTermForwardRootV1
