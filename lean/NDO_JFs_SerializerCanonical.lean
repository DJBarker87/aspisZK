import NDO_JFs_PublicValue
import PublicSerializerWhole431
import ExtractedDecoderPublicBinding
set_option autoImplicit false
namespace AspisR1.JFs_SerializerCanonical
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Frontier431
open AspisR1PublicSerializer.Whole431

def value : Public := AspisR1TerminalDecoder.PublicBinding.toSerializer JFs_PublicValue.value

theorem digest (a : Array U32 8#usize) (hc : JFu_DigestCanonical.Canonical a) : canonical a.val := by
  intro x hx
  obtain ⟨i,hi,same⟩:=List.mem_iff_getElem.mp hx
  rw [←same]
  apply hc ⟨i,by simpa only [a.property,show (8#usize).val=8 from rfl] using hi⟩

theorem append (xs ys : List Field) : canonical (xs++ys) ↔canonical xs ∧canonical ys := by
  constructor
  · intro h
    exact ⟨fun x hx=>h x (List.mem_append_left _ hx),fun x hx=>h x (List.mem_append_right _ hx)⟩
  · rintro ⟨hxs,hys⟩ x hx
    exact (List.mem_append.mp hx).elim (hxs x) (hys x)

theorem frontier (f : Frontier)
    (hc : ∀ i : Fin 20,JFu_DigestCanonical.Canonical
      (f.val[i.val]'(by rw [f.property];exact i.isLt))) :
    canonical ((rows f).flatMap (fun s => s.val)) := by
  have eq : rows f=(List.finRange 20).map (AspisR1PublicSerializer.Frontier431.row f) := by rfl
  intro x hx
  rw [eq] at hx
  obtain ⟨s,hs,hx⟩:=List.mem_flatMap.mp hx
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hs
  exact digest _ (hc i) x hx

theorem source : canonical ((sourceSteps value).flatMap stepWords) := by
  have c43:=digest _ JFt_Digest43.canonical
  have c44:=digest _ JFt_Digest44.canonical
  have c45:=digest _ JFt_Digest45.canonical
  have c46:=digest _ JFt_Digest46.canonical
  have c22:=digest _ JFt_Digest22.canonical
  have before:=frontier JFt_SnapshotValue.value.frontier
    (fun i => JFu_DigestSliceCanonical.source _ _ (JFt_SnapshotValue.frontier i))
  have after:=frontier JFt_AfterstateValue.value.next_frontier JFt_AfterstateValue.frontier
  have asset : canonical [JFs_PaymentValue.common.asset_id] := by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    change (core.num.U32.from_le_bytes JFs_Cell07.value).val<2147483647
    rw [JFs_PaymentValue.asset]
    decide
  change canonical (JFt_Digest43.value.val++(JFt_Digest44.value.val++
    ([JFs_PaymentValue.common.asset_id]++(JFt_Digest45.value.val++
    (JFt_Digest46.value.val++(((rows JFt_SnapshotValue.value.frontier).flatMap (fun s => s.val))++
    (JFt_Digest22.value.val++((rows JFt_AfterstateValue.value.next_frontier).flatMap (fun s => s.val)))))))))
  simp only [append]
  exact ⟨c43,c44,asset,c45,c46,before,c22,after⟩

#print axioms digest
#print axioms append
#print axioms frontier
#print axioms source
end AspisR1.JFs_SerializerCanonical
