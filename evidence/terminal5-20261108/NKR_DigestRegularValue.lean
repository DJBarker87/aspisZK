import NKR_DigestReads
import NKR_DigestOldPack
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestRegularValue
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJX_DigestCohort (O D ocells dcells dc)
open NKI_InitialPrefix (Selectors Openings)

def residual (o : O) (d : D) (g : Fin 2) : Fin 4 → K := fun j=>
 FIv_NativeArray.value o (NJX_DigestGroups.index g j).val-
  FIw_PublicModel.digest d (NJX_DigestGroups.index g j)

theorem left (high : NQ) (o : O) (d : D) (out : Fin 2 → NQ)
 (hh : Canon high) (ho : FIw_ArrayValue.canonical o) (hd : dc d)
 (call : NJX_DigestPacket.reference high (ocells o) (dcells d)=ok out) :
 ∀ g,decode (out g)=decode high*NJB_PackLinearity.pack (residual o d g) := by
 obtain ⟨packet,pc⟩ := NJX_DigestPacket.source high (ocells o) (dcells d) hh
  (fun j=>NJB_ArrayCarrier.canonical_cell o ho _) (fun j=>hd _ (List.getElem_mem _))
 have same : packet.out=out := Result.ok.inj (pc.symm.trans call)
 intro g
 rw [←same,packet.out_value]
 congr 1
 apply congrArg NJB_PackLinearity.pack
 funext j
 unfold residual ocells dcells
 rw [NKR_DigestReads.cell] <;> rfl

def row (i : Fin 64) : Fin 1024 := ⟨16*i.val+11,by have h:=i.isLt;omega⟩
def binding (s : Selectors) (o : O) (i : Fin 64) (d : D) (g : Fin 2) : K :=
 FIw_PublicModel.selector s (row i)*NJB_PackLinearity.pack (residual o d g)

theorem row_value (s : Selectors) (i : Fin 64) :
 FIw_PublicModel.selector s (row i)=decode (NKR_DigestChildren.high s i)*FIv_NativeArray.value s.low 11 := by
 have hd : (16*i.val+11)/16=i.val := by omega
 have hm : (16*i.val+11)%16=11 := by omega
 unfold FIw_PublicModel.selector row NKR_DigestChildren.high
 rw [NKR_DigestReads.cell]
 simp only [hd,hm]

theorem scaled (s : Selectors) (o : Openings) (i : Fin 64) (d : D) (out : Fin 2 → NQ)
 (hs : FIw_ArrayValue.canonical s.high) (ho : FIw_ArrayValue.canonical o.z) (hd : dc d)
 (call : NKR_DigestChildren.left s o i d=ok out) :
 ∀ g,binding s o.z i d g=FIv_NativeArray.value s.low 11*decode (out g) := by
 have value:=left (NKR_DigestChildren.high s i) o.z d out
  (NJB_ArrayCarrier.canonical_cell s.high hs _) ho hd call
 intro g
 rw [binding,row_value,value]
 ring
theorem scaled_cohort (s : Selectors) (o : Openings) (i : Fin 64) (d : D) (out : Fin 2 → NQ)
 (hs : FIw_ArrayValue.canonical s.high) (ho : FIw_ArrayValue.canonical o.z) (hd : dc d)
 (call : NJX_LeftRoot.cohort (NKR_DigestChildren.high s i) o.z d=ok out) :
 ∀ g,binding s o.z i d g=FIv_NativeArray.value s.low 11*decode (out g) := by
 obtain ⟨packet,pc,mc⟩ := NJX_LeftRoot.source (NKR_DigestChildren.high s i) o.z d
  (NJB_ArrayCarrier.canonical_cell s.high hs _) ho hd
 have same : packet.out=out := Result.ok.inj (mc.symm.trans call)
 have vals := scaled s o i d packet.out hs ho hd pc
 rw [same] at vals
 exact vals
#print axioms scaled_cohort
#print axioms left
#print axioms row_value
#print axioms scaled
end AspisR1.NKR_DigestRegularValue
end
