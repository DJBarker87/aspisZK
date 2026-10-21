import S4CurrentHeadTermForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsHeadBatchTermsForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops M31)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide TermBody ReadWitness)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (Range cap cell)
open AspisR1FastDotsCurrentHeadTermForwardRootV1 (install current_term_body_forward)
abbrev TermLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0

def ParsedAt (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) : Prop :=
  ∃ r : ReadWitness a g slot term, ∃ scalar : M31,
    AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes r.copied = .ok (some scalar)

theorem selected_coefficient_canonical
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot term : Usize)
    (r : ReadWitness a g slot term) (ht : term.val<26)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt))) :
    AspisR1FastDotsWideLimbCanonical.CoordinateBound r.coefficient := by
  obtain ⟨x,hr,hx⟩ := WP.spec_imp_exists
    (Array.index_usize_spec g term (by simpa [Array.length,g.property] using (show term.val<29 by omega)))
  have he : r.coefficient=x := Result.ok.inj (r.hread.symm.trans hr)
  rw [he,hx]
  exact hcoords ⟨term.val,by omega⟩

theorem term_loop_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot start finish : Usize) (sums : Array Std.U64 8#usize) (k : Nat)
    (hs : start.val≤finish.val) (hf : finish.val≤26)
    (hbudget : k+(finish.val-start.val)≤4)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hparsed : ∀ term : Usize, start.val≤term.val → term.val<finish.val → ParsedAt a g slot term)
    (hinput : ∀ j : Fin 8, cell sums j≤k*cap) :
    ∃ out : Array Std.U64 8#usize,
      TermLoop (install base) {start:=start,«end»:=finish} a g slot sums = .ok out ∧
      (∀ j : Fin 8, cell out j≤(k+(finish.val-start.val))*cap) := by
  induction hm : finish.val-start.val using Nat.strong_induction_on generalizing start sums k with
  | h m ih =>
    by_cases he : start.val=finish.val
    · have heq : start=finish := UScalar.eq_of_val_eq he
      subst start
      obtain ⟨it,hn⟩ := AspisR1FastDotsTailRangeNextRootV1.range_next_done finish
      have hb : TermBody (install base) a g slot {start:=finish,«end»:=finish} sums =
          .ok (.done sums) := by
        simp [TermBody,
          AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body,hn]
      refine ⟨sums,?_,?_⟩
      · change loop (fun st : Range × Array Std.U64 8#usize =>
          TermBody (install base) a g slot st.1 st.2)
          ({start:=finish,«end»:=finish},sums) = .ok sums
        rw [loop.eq_def]
        simpa only [hb,bind_tc_ok]
      · have hm0 : m=0 := by omega
        rw [hm0,Nat.add_zero]
        exact hinput
    · have hi : start.val<finish.val := by omega
      have hk : k≤3 := by omega
      obtain ⟨next,_ha,hv⟩ := AspisR1FastDotsFirstTailReadTotalRootV1.small_checked_add start 1#usize
        (by change start.val+1<1024; omega)
      have hv' : next.val=start.val+1 := by simpa using hv
      have hn := AspisR1FastDotsTailRangeNextRootV1.range_next_succ start finish next hi hv'
      obtain ⟨r,scalar,hp⟩ := hparsed start (Nat.le_refl _) hi
      have hc := selected_coefficient_canonical a g slot start r (by omega) hcoords
      obtain ⟨updated,hb,hbnd⟩ := current_term_body_forward base k hk a g slot start
        {start:=start,«end»:=finish} {start:=next,«end»:=finish} sums r scalar hn hp hc hinput
      have hparseNext : ∀ term : Usize, next.val≤term.val → term.val<finish.val → ParsedAt a g slot term := by
        intro term ht he
        exact hparsed term (by omega) he
      obtain ⟨out,hl,ho⟩ := ih (finish.val-next.val) (by omega) next updated (k+1)
        (by omega) (by omega) hparseNext hbnd rfl
      refine ⟨out,?_,?_⟩
      · change loop (fun st : Range × Array Std.U64 8#usize =>
          TermBody (install base) a g slot st.1 st.2)
          ({start:=next,«end»:=finish},updated) = .ok out at hl
        change loop (fun st : Range × Array Std.U64 8#usize =>
          TermBody (install base) a g slot st.1 st.2)
          ({start:=start,«end»:=finish},sums) = .ok out
        rw [loop.eq_def]
        simpa only [hb,bind_tc_ok] using hl
      · have heq : k+m=(k+1)+(finish.val-next.val) := by omega
        rw [heq]
        exact ho

#print axioms selected_coefficient_canonical
#print axioms term_loop_forward
end AspisR1FastDotsHeadBatchTermsForwardRootV1
