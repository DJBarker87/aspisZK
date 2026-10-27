import R1Z.PV_Inv_RawBankList
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_RawBankTuple
open Aeneas Aeneas.Std Result
open ProverCommitM31Ops48
open ProverCommitScalar48 (embed)
open AspisR1.ExtractedCurrentQM31Exact (QM31Exact)
open PV_Inv_BankSource PV_Inv_RawBankRead

theorem tuple_read (b : Banks U32) (hb : CanonicalBanks b) (ls : Fin 16 → Limb U32)
    (hl : ∀ i, CanonicalLimb (ls i)) :
    ∃ words : Fin 16 → U32,
      PV_Inv_RawBankList.reads b (List.ofFn ls) = ok (List.ofFn words) ∧
      (∀ i, canonical (words i)) ∧
      (∀ i, embed (words i) = PV_Inv_BankSource.read (banks b) (limb (ls i))) := by
  obtain ⟨zs,hr,hc,hv⟩ := PV_Inv_RawBankList.exact_reads b hb (List.ofFn ls) (by
    intro l he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact hl i)
  have hlen : zs.length=16 := by
    have h := congrArg List.length hv
    simpa only [List.length_map,List.length_ofFn] using h
  let words : Fin 16 → U32 := fun i => zs[i.val]'(by rw [hlen];exact i.isLt)
  have hw : List.ofFn words=zs := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hlen.symm
    · intro i hi hj
      simp only [List.getElem_ofFn,words]
  refine ⟨words,by rw [hw];exact hr,?_,?_⟩
  · intro i
    exact hc _ (List.getElem_mem _)
  · intro i
    have h := congrArg (fun xs : List QM31Exact => xs[i.val]?) hv
    simpa only [List.getElem?_map,List.getElem?_ofFn,i.isLt,↓reduceDIte,
      List.getElem?_eq_getElem (by rw [hlen];exact i.isLt),Option.map_some,Option.some.injEq,
      words] using h

#print axioms tuple_read
end R1Z.PV_Inv_RawBankTuple
