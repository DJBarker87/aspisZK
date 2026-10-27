import XRl_DotHistory
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRl_DotSums
abbrev Operand := fast_pairing.canonical.Q × fast_pairing.canonical.Q

def cellStep (j : Fin 4) (s : U64) (v : Operand) : U64 :=
  XRk_u64 (s.val + XRk_partial ((XRk_raw v.1 v.2)[j.val]?.getD 0))
inductive DotTrace : List Operand → fast_pairing.canonical.Dot → Prop
  | initial : DotTrace [] XRk_dotZero
  | push {xs : List Operand} {old next : fast_pairing.canonical.Dot}
      (prior : DotTrace xs old) (a b : fast_pairing.canonical.Q)
      (run : fast_pairing.canonical.Dot.push old a b=ok next) :
      DotTrace (xs++[(a,b)]) next

theorem cells (xs : List Operand) (s : fast_pairing.canonical.Dot) (history : DotTrace xs s)
    (j : Fin 4) : s.sums.val[j.val]?.getD 0#u64 = xs.foldl (cellStep j) 0#u64 := by
  induction history with
  | initial =>
    change (List.replicate 4 0#u64)[j.val]?.getD 0#u64 = 0#u64
    simp only [List.getElem?_replicate,if_pos j.isLt,Option.getD_some]
  | push prior a b run ih =>
    rw [XRk_DotCells.sum_cell _ _ a b j run,ih]
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,cellStep]

/-- Both raw dot histories belong to the SAME source accepted-push history.
Each scalar and wide projection is selected from that actual push, rather
than an independent output witness. -/
def Converts (v : XRl_DotHistory.Input)
    (a b q : fast_pairing.canonical.Q) : Prop :=
  ∃ wide, fast_pairing.canonical.Q.from_wide v.1=ok wide ∧
    Array.index_usize wide 0#usize=ok a ∧ Array.index_usize wide 1#usize=ok b ∧
    fast_pairing.checked_q v.2=ok (.Ok q)

inductive Operands : List XRl_DotHistory.Input → List (fast_pairing.canonical.Q × fast_pairing.canonical.Q × fast_pairing.canonical.Q) → Prop
  | nil : Operands [] []
  | append {xs ops} (prior : Operands xs ops) (v : XRl_DotHistory.Input)
      (a b q : fast_pairing.canonical.Q) (converts : Converts v a b q) :
      Operands (xs++[v]) (ops++[(a,b,q)])

theorem factor (xs : List XRl_DotHistory.Input) (s : fast_pairing.EbyKDot)
    (history : XRl_DotHistory.Reached xs s) :
    ∃ ops, Operands xs ops ∧ DotTrace (ops.map (fun v => (v.1,v.2.2))) s.c0 ∧
      DotTrace (ops.map (fun v => (v.2.1,v.2.2))) s.c1 := by
  induction history with
  | initial s run =>
    have same := Result.ok.inj run
    have h0 : s.c0=XRk_dotZero := congrArg fast_pairing.EbyKDot.c0 same.symm
    have h1 : s.c1=XRk_dotZero := congrArg fast_pairing.EbyKDot.c1 same.symm
    exact ⟨[],.nil,by simpa only [h0,List.map_nil] using DotTrace.initial,
      by simpa only [h1,List.map_nil] using DotTrace.initial⟩
  | push prior e q run ih =>
    obtain ⟨ops,hop,h0,h1⟩ := ih
    obtain ⟨_,wide,a,b,raw,hw,ha,hb,hq,hd0,hd1,_⟩ := XRk_PushTrace.accepted _ _ e q run
    refine ⟨ops++[(a,b,raw)],.append hop (e,q) a b raw ⟨wide,hw,ha,hb,hq⟩,?_,?_⟩
    · simpa only [List.map_append,List.map_cons,List.map_nil] using DotTrace.push h0 a raw hd0
    · simpa only [List.map_append,List.map_cons,List.map_nil] using DotTrace.push h1 b raw hd1

#print axioms cells
#print axioms factor
end XRl_DotSums
