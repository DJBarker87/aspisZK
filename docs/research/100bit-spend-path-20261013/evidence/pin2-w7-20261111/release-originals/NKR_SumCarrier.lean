import NKR_SumCuts
import NJB_ArrayCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCarrier
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (decode Canon)
abbrev A4 := Array NQ 4#usize

def back (x : NKR_SumDispatch.Q) : NQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def encode {N : Usize} (x : Array NQ N) : Array NKR_SumDispatch.Q N :=
 ⟨x.val.map qm,by simp only [List.length_map,x.property]⟩

theorem roundtrip (x : NKR_SumDispatch.Q) : qm (back x)=x := by
 cases x with | mk a b => cases a;cases b;rfl

theorem back_roundtrip (x : NQ) : back (qm x)=x := by
 cases x with | mk a b => cases a;cases b;rfl

theorem encoded_canonical {N : Usize} (x : Array NQ N) (hx : FIw_ArrayValue.canonical x) :
 ∀ q∈(encode x).val,NKR_SumDispatch.Canon q := by
 intro q hq
 obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
 exact hx v hv

def reference (l r : A4) (count : Nat) : Result NQ :=
 FIv_Map.map back (NKR_SumDispatch.reference (encode l) (encode r) count)

def native (l r : A4) (count : Nat) : Result NQ :=
 FIv_Map.map back (NKR_SumDispatch.native (encode l) (encode r) count)

/-- The225 terminal carrier preserves all four raw M31 words. Canonical
helper arguments and n+remaining<=4 are discharged at the SAME arrays.
Native cut/root packet credit awaits the parent's native PASS/FAIL pair
and the combined/next-ledger gates. -/
theorem source (l r : A4) (count : Nat) (lower : 1≤count) (upper : count≤4)
 (hl : FIw_ArrayValue.canonical l) (hr : FIw_ArrayValue.canonical r) :
 ∃ out,native l r count=ok out ∧ reference l r count=ok out ∧ Canon out ∧
 decode out=NGA_SumAlgebra.sumProducts (((encode l).val.zip (encode r).val).take count) ∧
 ∀ (seek : Fin 4),seek.val<count →
 NKR_SumCuts.Cut (encode l) (encode r) count seek (qm out) (qm out)
 (NGA_Indexed.selected (encode l) seek) (NGA_Indexed.selected (encode r) seek) 1 count := by
 obtain ⟨out,hn,href,hco,hc,hv,cut⟩ := NKR_SumCuts.source (encode l) (encode r) count lower upper
  (encoded_canonical l hl) (encoded_canonical r hr)
 refine ⟨back out,?_,?_,?_,?_,?_⟩
 · simp only [native,hn,FIv_Map.map_ok]
 · simp only [reference,href,FIv_Map.map_ok]
 · change NKR_SumDispatch.Canon (qm (back out))
   rw [roundtrip]
   exact hc
 · change AspisR1.ExtractedMaskQM31Exact.decode (qm (back out))=_
   rw [roundtrip]
   exact hv
 · rw [roundtrip]
   exact cut

#print source
#print axioms roundtrip
#print axioms back_roundtrip
#print axioms encoded_canonical
#print axioms source
end AspisR1.NKR_SumCarrier
end
