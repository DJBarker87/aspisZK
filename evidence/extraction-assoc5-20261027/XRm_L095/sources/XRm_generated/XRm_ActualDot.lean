import XRm_DotNaturalHistory
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace XRm_ActualDot
/-- Producer-to-push association with BOTH canonical operand halves and
non-wrapping natural sums, for the SAME accepted emitted tail. -/
theorem associated {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (old scratch : Array XRk_Wide 29#usize) (prepared : verifier.Prepared)
    (prepare : verifier.Prepared.new D sem view hash old=ok (.Ok prepared,scratch))
    (q : Array U8 608#usize) (slot : Usize) (out : XRk_Wide)
    (run : fast_dots.four_dots_one q scratch slot=ok out) :
    ∃ xs d ops,
      XRl_DotHistory.Reached xs d ∧ xs.length=3 ∧ d.count.val=3 ∧
      (∀ v ∈ xs, XRl_WideCanonical.Canonical v.1 ∧ XRk_CanonicalScalar.Canonical v.2) ∧
      XRl_DotSums.Operands xs ops ∧ ∀ j : Fin 4,
        (d.c0.sums.val[j.val]?.getD 0#u64).val=
          (ops.map (fun v => (v.1,v.2.2))).foldl (XRm_DotNoWrap.natStep j) 0 ∧
        (d.c1.sums.val[j.val]?.getD 0#u64).val=
          (ops.map (fun v => (v.2.1,v.2.2))).foldl (XRm_DotNoWrap.natStep j) 0 := by
  obtain ⟨xs,d,history,size,count,bound,canonical,_⟩ :=
    XRm_DotAssociation.prepared_tail D sem view hash old scratch prepared prepare q slot out run
  obtain ⟨ops,hop,_,cells⟩ := XRm_DotNaturalHistory.reached xs d history
  exact ⟨xs,d,ops,history,size,count,canonical,hop,cells⟩
#print axioms associated
end XRm_ActualDot
