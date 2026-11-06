import NJX_InitialPrologue
import NJL_Traverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_InitialLane
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
open NJX_InitialPrologue (Selectors)
def cache {s : Selectors} {v : NJX_InitialVariant.Variant} {nodes : NQ}
 (p : NJX_InitialPrologue.Packet s v nodes) (i : Fin 16) : NP := if i.val<8 then p.both else p.full
def scale {s : Selectors} {v : NJX_InitialVariant.Variant} {nodes : NQ}
 (p : NJX_InitialPrologue.Packet s v nodes) (i : Fin 16) : NQ := if i.val<8 then p.bothValue else p.fullValue

theorem domain {s : Selectors} {v : NJX_InitialVariant.Variant} {nodes : NQ}
 (p : NJX_InitialPrologue.Packet s v nodes) (i : Fin 16) :
 Canon (scale p i) ∧ NJB_PreparedLaws.Domain (cache p i) (scale p i) := by
 obtain ⟨_,_,_,_,hf,hb⟩ := p.canonical
 unfold cache scale
 split
 · exact ⟨hb,p.domain2⟩
 · exact ⟨hf,p.domain1⟩

def reference {s : Selectors} {v : NJX_InitialVariant.Variant} {nodes : NQ}
 (p : NJX_InitialPrologue.Packet s v nodes) (o : Array NQ 16#usize) (i : Fin 16) : Result NQ :=
 FIq_Native.field.PreparedQm31Multiplier.mul (cache p i) (NJB_ArrayCarrier.cell o ⟨i.val,by have h:=i.isLt;scalar_tac⟩)
/-- All16actual initial lane callbacks, SAME actual two constructor caches,
no cache-validity hypothesis. Writes8/9 and absorption caller remain OPEN260. -/
theorem source {s : Selectors} {v : NJX_InitialVariant.Variant} {nodes : NQ}
 (p : NJX_InitialPrologue.Packet s v nodes) (o : Array NQ 16#usize) (ho : FIw_ArrayValue.canonical o) :
 ∃ ys,NJB_Traverse.run (reference p o) (List.finRange 16)=ok ys ∧ (∀ y∈ys.val,Canon y) ∧
 List.Forall₂ (fun i y=>reference p o i=ok y) (List.finRange 16) ys.val := by
 apply NJL_Traverse.packet
 intro i _
 obtain ⟨y,cy,hy,_⟩ := NJB_PreparedLaws.mul_result (cache p i) (scale p i) _ (domain p i).1
  (NJB_ArrayCarrier.canonical_cell o ho _) (domain p i).2
 exact ⟨y,cy,hy,cy⟩
#print source
#print axioms domain
#print axioms source
end AspisR1.NJX_InitialLane
end
