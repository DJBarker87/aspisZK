import NFT_Pack
import NJB_ArrayCarrier
import NJB_StubLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_PackLaw
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon decode K)
abbrev PQ := AspisR1SelectedMaskProbe.field.QM31
def raw (p : PQ) : NQ := ⟨⟨⟨p.c0.a.0⟩,⟨p.c0.b.0⟩⟩,⟨⟨p.c1.a.0⟩,⟨p.c1.b.0⟩⟩⟩
theorem qm_raw (p : PQ) : qm (raw p)=p := by cases p with | mk a b => cases a;cases b;rfl
def slice (v : Fin 4 → NQ) : Slice PQ :=
 ⟨List.ofFn (fun i=>qm (v i)),by simp;scalar_tac⟩
theorem length (v : Fin 4 → NQ) : (slice v).length=4 := by simp [slice,Slice.length]
def reference (v : Fin 4 → NQ) : Result NQ :=
 FIv_Map.map raw (AspisR1SelectedMaskProbe.field.qm31_pack_base4 (slice v))
def model (v : Fin 4 → NQ) : K :=
 ExtractedMaskQmPackBase4Arithmetic.mathematicalPack (fun i=>qm (v i))
theorem result (v : Fin 4 → NQ) (hv : ∀ i,Canon (v i)) :
 ∃ out,reference v=ok out ∧ Canon out ∧ decode out=model v := by
 have short : (slice v).length≤4 := by rw [length]
 have canonical : ∀ q∈(slice v).val,ExtractedMaskTowerAdd.CanonicalQM q := by
  intro q h
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp h
  simpa only [←hi] using hv i
 obtain ⟨p,call,hp,vp⟩ := NFT_Pack.source (slice v) short canonical
 refine ⟨raw p,?_,?_,?_⟩
 · simp only [reference,call,FIv_Map.map]
 · change ExtractedMaskQM31Exact.CurrentCanonicalQM (qm (raw p))
   simpa only [qm_raw] using hp
 · change ExtractedMaskQM31Exact.decode (qm (raw p))=model v
   rw [qm_raw,vp]
   congr 1
   funext i
   simp [NFT_Pack.Whole,NFT_Pack.paddedSlice,NFT_Pack.padded,
    ExtractedMaskQmPackBase4Whole.inputAt,slice,length,Array.to_slice]
#print result
#print axioms qm_raw
#print axioms length
#print axioms result
end AspisR1.NJB_PackLaw
end
