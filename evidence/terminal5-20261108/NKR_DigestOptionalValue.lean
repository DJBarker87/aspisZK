import NKR_DigestKeyValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestOptionalValue
open Aeneas Aeneas.Std Result
open FIv_NativeValue (decode K)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestChildren (Children Clauses)
open NKR_DigestKeyValues (term)

def recipientKeys (p : Public) : List R0P.DigestKey :=
 match p.recipient with | none=>[] | some _=>[.recipient]
def carryKeys (p : Public) : List R0P.DigestKey :=
 if R0P.digestCarry p.transition.live_snapshot.next_pair_index.val<20 then [.carry] else []

theorem recipient (p : Public) (o : Openings) (s : Selectors) (c : Children)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hc : Clauses p o s c) (g : Fin 2) :
 ((recipientKeys p).map (fun key=>term p o s key g)).sum=
 FIv_NativeArray.value s.low 11*decode (c.recipient g) := by
 obtain ⟨_,_,_,_,_,rm,_⟩ := hc
 cases hr : p.recipient with
 | none=>
   have eq : NJX_RecipientRoot.zero=c.recipient := by
    apply Result.ok.inj
    simpa only [NJX_RecipientRoot.cohort,hr] using rm
   rw [←eq]
   simp only [recipientKeys,hr,List.map_nil,List.sum_nil,NJX_RecipientRoot.zero,FIv_NativeValue.zero.2,mul_zero]
 | some d=>
   have call : NJX_LeftRoot.cohort (NKR_DigestChildren.high s 29) o.z d=ok c.recipient := by
    simpa only [NJX_RecipientRoot.cohort,hr] using rm
   have scaled:=NKR_DigestRegularValue.scaled_cohort s o 29 d c.recipient hh ho (hp.recipient d hr) call g
   simpa only [recipientKeys,hr,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    term,NKR_DigestOldPack.contribution,R0P.digestRow,R0P.digestStart,R0P.digestTarget,FIw_PublicModel.ofPublic,
    FIw_PublicModel.openings,NKR_DigestRegularValue.binding,NKR_DigestRegularValue.row,NKR_DigestRegularValue.residual,
    Option.map_some,Option.getD_some,show (0 : Fin 9).val=0 from rfl,Nat.zero_add] using scaled

theorem carry (p : Public) (o : Openings) (s : Selectors) (c : Children)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hc : Clauses p o s c) (g : Fin 2) :
 ((carryKeys p).map (fun key=>term p o s key g)).sum=
 FIv_NativeArray.value s.low 11*decode (c.carried g) := by
 obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,cv,bound,_,cam⟩ := hc
 by_cases active : c.carry.val<20
 · have minc : min c.carry.val 19=c.carry.val := Nat.min_eq_left (by omega)
   let i : Fin 64:=⟨33+c.carry.val,by omega⟩
   let d:=NJX_AppendDomains.frontier p.transition.candidate_afterstate.next_frontier (NKI_PublicDomains.carryLevel c.carry.val)
   have high : NKI_PublicDomains.high s c.carry.val=NKR_DigestChildren.high s i := by
    simp only [NKI_PublicDomains.high,NKR_DigestChildren.high,NKI_PublicDomains.carryLevel,minc,i]
   have call : NJX_LeftRoot.cohort (NKR_DigestChildren.high s i) o.z d=ok c.carried := by
    simpa only [NJX_CarryRoot.cohort,if_pos active,high,d] using cam
   have hd : NJX_DigestCohort.dc d := hp.nextFrontier _ (List.getElem_mem _)
   have scaled:=NKR_DigestRegularValue.scaled_cohort s o i d c.carried hh ho hd call g
   have enabled : R0P.digestCarry p.transition.live_snapshot.next_pair_index.val<20 := by rw [←cv];exact active
   simpa only [carryKeys,if_pos enabled,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    term,NKR_DigestOldPack.contribution,R0P.digestRow,R0P.digestStart,R0P.digestTarget,FIw_PublicModel.ofPublic,
    FIw_PublicModel.openings,NKR_DigestRegularValue.binding,NKR_DigestRegularValue.row,NKR_DigestRegularValue.residual,
    R0P.g2Row,if_pos enabled,show (0 : Fin 9).val=0 from rfl,Nat.zero_add,←cv,
    d,NJX_AppendDomains.frontier,NKI_PublicDomains.carryLevel,minc,NJB_ArrayCarrier.cell,FIw_PublicModel.digest,i,
    Nat.mul_comm] using scaled
 · have eq : NJX_CarryRoot.zero=c.carried := by
    apply Result.ok.inj
    simpa only [NJX_CarryRoot.cohort,if_neg active] using cam
   have disabled : ¬R0P.digestCarry p.transition.live_snapshot.next_pair_index.val<20 := by rw [←cv];exact active
   rw [←eq]
   simp only [carryKeys,if_neg disabled,List.map_nil,List.sum_nil,NJX_CarryRoot.zero,FIv_NativeValue.zero.2,mul_zero]
#print axioms recipient
#print axioms carry
end AspisR1.NKR_DigestOptionalValue
end
