import FourDotsActualTailInputMeaningRootV1
import S4TailFieldProductRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4TailCoefficientPowersV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1
open AspisR1FastDotsActualTailLoopTraceRootV1
open AspisR1FastDotsActualTailInputMeaningRootV1
open AspisR1FastDotsTailFieldProductRootV1
abbrev Range := core.ops.range.Range Usize

theorem index_success_value (g : Array Wide 29#usize) (i : Usize) (x : Wide)
    (h : Array.index_usize g i = .ok x) :
    ∃ hb : i.val < g.val.length, g.val[i.val]'hb = x := by
  have hb : i.val < g.val.length := by
    by_contra hn
    have hnone : g[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hn)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  refine ⟨hb,?_⟩
  have hget : g[i]? = some (g.val[i.val]'hb) := List.getElem?_eq_getElem hb
  unfold Array.index_usize at h
  rw [hget] at h
  exact Result.ok.inj h

theorem index_success_power (g : Array Wide 29#usize) (i : Usize) (x : Wide)
    (gamma : TowerWide)
    (hpowers : ∀ j : Fin 29, wideDecoded (g.val[j.val]'(by scalar_tac)) = gamma ^ j.val)
    (hget : Array.index_usize g i = .ok x) : wideDecoded x = gamma ^ i.val := by
  obtain ⟨hb,hvalue⟩ := index_success_value g i x hget
  have hi29 : i.val < 29 := by simpa [g.property] using hb
  have hp := hpowers ⟨i.val,hi29⟩
  rw [hvalue] at hp
  exact hp

theorem source_meaning_coefficient_power
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (gamma : TowerWide) (c : Contribution)
    (hpowers : ∀ j : Fin 29, wideDecoded (g.val[j.val]'(by scalar_tac)) = gamma ^ j.val)
    (hc : SourceMeaning a g slot c) :
    wideDecoded c.coefficient = gamma ^ (26+c.term.val) := by
  obtain ⟨i,hi,hget,hbytes⟩ := hc
  have hp := index_success_power g i c.coefficient gamma hpowers hget
  simpa only [hi, Nat.add_comm] using hp

theorem tail_trace_coefficient_powers
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (old out : Tail) (cs : List Contribution) (gamma : TowerWide)
    (hpowers : ∀ j : Fin 29, wideDecoded (g.val[j.val]'(by scalar_tac)) = gamma ^ j.val)
    (htrace : RunTrace ops a g slot iter old out cs) :
    ∀ c ∈ cs, wideDecoded c.coefficient = gamma ^ (26+c.term.val) := by
  intro c hc
  exact source_meaning_coefficient_power a g slot gamma c hpowers
    (actual_tail_trace_source_meanings ops a g slot iter old out cs htrace c hc)
#print axioms index_success_value
#print axioms index_success_power
#print axioms source_meaning_coefficient_power
#print axioms tail_trace_coefficient_powers
end AspisR1.S4TailCoefficientPowersV1
