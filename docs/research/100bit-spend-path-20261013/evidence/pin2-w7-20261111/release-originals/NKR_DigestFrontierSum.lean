import NKR_DigestPrefix
import NKR_DigestAppendValue
import NKR_DigestKeyValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestFrontierSum
open Aeneas Aeneas.Std Result
open FIv_NativeValue (decode K)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestChildren (Children Clauses)
open NKR_DigestKeyValues (term)

theorem sum_mix {α : Type} (xs : List α) (a b : K) (x y : α → K) :
 (xs.map (fun i=>a*x i+b*y i)).sum=a*(xs.map x).sum+b*(xs.map y).sum := by
 induction xs with
 | nil=>simp
 | cons i xs ih=>
   simp only [List.map_cons,List.sum_cons,ih]
   ring

theorem source (p : Public) (o : Openings) (s : Selectors) (c : Children)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hc : Clauses p o s c) (g : Fin 2) :
 ((List.ofFn R0P.DigestKey.frontier).map (fun key=>term p o s key g)).sum=
 NKR_DigestAppendValue.low0 s*decode (NKR_DigestPrefix.first c.levels g)+
 NKR_DigestAppendValue.low12 s*decode (NKR_DigestPrefix.last c.levels g) := by
 obtain ⟨_,_,_,_,_,_,_,_,lc,_⟩ := hc
 obtain ⟨packets,out,_,call,_,_,values⟩ := NKI_LevelsRoot.source p.transition.live_snapshot.next_pair_index
  p.transition.live_snapshot.frontier o.z s.high hp.frontier ho hh
 have same : out=c.levels := Result.ok.inj (call.symm.trans lc)
 rw [same] at values
 have keyvalue : ∀ i : Fin 20,term p o s (.frontier i) g=
  NKR_DigestAppendValue.low0 s*decode (NKI_AppendPacket.output (packets i) ⟨g.val,by have h:=g.isLt;omega⟩)+
  NKR_DigestAppendValue.low12 s*decode (NKI_AppendPacket.output (packets i) ⟨2+g.val,by have h:=g.isLt;omega⟩) := by
  intro i
  unfold term NKR_DigestOldPack.contribution
  rw [←NJB_PackLinearity.scale]
  have lanes : (fun j : Fin 4=>FIw_PublicModel.selector s (R0P.digestRow (FIw_PublicModel.ofPublic p) (.frontier i))*
    ((FIw_PublicModel.openings o).z ⟨(R0P.digestStart (FIw_PublicModel.ofPublic p) (.frontier i)).val+(NJX_DigestGroups.index g j).val,by have h:=(R0P.digestStart (FIw_PublicModel.ofPublic p) (.frontier i)).isLt;have h':=(NJX_DigestGroups.index g j).isLt;omega⟩-
     R0P.digestTarget (FIw_PublicModel.ofPublic p) (.frontier i) (NJX_DigestGroups.index g j)))=
    (fun j=>FIy_FrontierMeaning.increment p.transition.live_snapshot s o.z i.val (NJX_DigestGroups.index g j).val) := by
   funext j
   exact (FIz_DigestFrontier.value p o s i _).symm
  rw [lanes]
  exact NKR_DigestAppendValue.packed p o s i packets g
 have summed : ((List.ofFn R0P.DigestKey.frontier).map (fun key=>term p o s key g)).sum=
  ((List.finRange 20).map (fun i=>
   NKR_DigestAppendValue.low0 s*decode (NKI_AppendPacket.output (packets i) ⟨g.val,by have h:=g.isLt;omega⟩)+
   NKR_DigestAppendValue.low12 s*decode (NKI_AppendPacket.output (packets i) ⟨2+g.val,by have h:=g.isLt;omega⟩))).sum := by
  simp only [List.finRange,List.map_ofFn]
  apply congrArg List.sum
  apply congrArg List.ofFn
  funext i
  exact keyvalue i
 rw [summed,sum_mix]
 have first : NKR_DigestPrefix.first c.levels g=c.levels ⟨g.val,by have h:=g.isLt;omega⟩ := by fin_cases g <;> rfl
 have last : NKR_DigestPrefix.last c.levels g=c.levels ⟨2+g.val,by have h:=g.isLt;omega⟩ := by fin_cases g <;> rfl
 rw [first,last,values,values]
#print axioms sum_mix
#print axioms source
end AspisR1.NKR_DigestFrontierSum
end
