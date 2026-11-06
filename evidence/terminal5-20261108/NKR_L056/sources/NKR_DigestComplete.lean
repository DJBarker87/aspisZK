import NKR_DigestPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestComplete
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode K)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestChildren (Pair Children Clauses Canonical)

def reference (p : Public) (o : Openings) (s : Selectors) : Result Pair := do
 let (_,sums)←NKR_DigestPrefix.run p o s
 NKI_LowMixFold.run (NKI_LowMixCaller.low s) sums (List.finRange 3) NKI_LowMixCaller.zero

/-- Mathematical packed expression for the complete three-group return.
Its association with the adopted whole-old public_digest_lanes remains a
separate obligation; this definition does not silently replace that cohort. -/
def model (s : Selectors) (c : Children) (j : Fin 2) : K :=
 decode (NKI_LowMixCaller.low s 0)*decode (NKR_DigestPrefix.first c.levels j)+
 decode (NKI_LowMixCaller.low s 1)*
  (decode (c.anchor j)+decode (c.nullifier j)+decode (c.recipient j)+
    decode (c.change j)+decode (c.nextRoot j)+decode (c.carried j))+
 decode (NKI_LowMixCaller.low s 2)*decode (NKR_DigestPrefix.last c.levels j)

/-- Complete source-reference result. All same-call child Results and their
canonical domains are derived, including carry20, optional recipient,20level
full4cell return and all three low-cache suffixes. Native251 parent-window
and adopted whole-old cohort association are NOT asserted by this theorem. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ c sums out,Clauses p o s c ∧ Canonical c ∧
 NKR_DigestPrefix.run p o s=ok (c,sums) ∧ NKR_DigestPrefix.Frame c sums ∧
 reference p o s=ok out ∧ (∀ j,Canon (out j)) ∧
 ∀ j,decode (out j)=model s c j := by
 obtain ⟨c,sums,pc,hc,hcan,hs,frame⟩ := NKR_DigestPrefix.source p o s hp ho hh
 obtain ⟨out,lowc,hout,vout⟩ := NKI_LowMixCaller.source s sums hl hs
 refine ⟨c,sums,out,hc,hcan,pc,frame,?_,hout,?_⟩
 · simp only [reference,pc,bind_tc_ok]
   exact lowc
 · intro j
   have v:=vout j
   rw [show List.finRange 3=[0,1,2] from by decide] at v
   simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at v
   rw [frame.values0,frame.values11,frame.values12] at v
   rw [v]
   unfold model
   ring
#print source
#print axioms source
end AspisR1.NKR_DigestComplete
end
