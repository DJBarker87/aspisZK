import RPz7_PAln_RowBounds
import R1FoldedLeafCodec
set_option autoImplicit false
namespace AspisR1.PAln_FieldRead
open AspisV8R19.DuplexFrames OraclePortCompactDraft
open RetainedFieldByteCodec StrictWideByteCodec

theorem slice_ofFn {n : Nat} (f : Fin n → (Fin 256)) (offset width : Nat)
    (bound : offset+width≤n) :
    slice (List.ofFn f) offset width=
      List.ofFn (fun i : Fin width => f ⟨offset+i.val,by omega⟩) := by
  apply List.ext_getElem
  · simp only [slice,List.length_take,List.length_drop,List.length_ofFn];omega
  · intro i hi hj
    simp only [slice,List.getElem_take,List.getElem_drop,List.getElem_ofFn]

theorem word_bound {n : Nat} (f : Fin n → (Fin 256)) (canonical : canonical (List.ofFn f))
    (j : Nat) (bound : 4*(j+1)≤n) :
    (decodeWordLE (fun i : Fin 4 => f ⟨4*j+i.val,by omega⟩)).val<m31Modulus := by
  have h := canonical.2 j (by simp only [List.mem_range,List.length_ofFn];omega)
  rw [slice_ofFn _ _ _ (by omega),MultiproofConeEndian.little_four] at h
  exact h

theorem qm31_exists (f : QM31Bytes) (checked : canonical (List.ofFn f)) :
    ∃ limbs, decodeQM31LE f=some limbs := by
  have bound : ∀ limb : Fin 4,
      (decodeWordLE (qm31LimbBytes f limb)).val<m31Modulus := by
    intro limb
    have h := word_bound f checked limb.val (by omega)
    have same : qm31LimbBytes f limb=(fun i : Fin 4 => f ⟨4*limb.val+i.val,by omega⟩) := by
      funext i
      unfold qm31LimbBytes
      apply congrArg f
      apply Fin.ext
      change i.val+4*limb.val=4*limb.val+i.val
      omega
    rw [same]
    exact h
  exact ⟨fun limb => ⟨decodeWordLE (qm31LimbBytes f limb),bound limb⟩,
    by simp only [decodeQM31LE,dif_pos bound]⟩

theorem wideLE_exists (f : WideBytes) (checked : canonical (List.ofFn f)) :
    ∃ limbs, decodeWideLE f=some limbs := by
  have parts := (MultiproofConeCanonicalAppend.canonical_take_drop
    (List.ofFn f) 16 (by decide) (by simp)).mp checked
  have low : List.ofFn (lowBytes f)=(List.ofFn f).take 16 := by
    have eq := slice_ofFn f 0 16 (by decide)
    simp only [slice,List.drop_zero,Nat.zero_add] at eq
    rw [eq]
    rfl
  have high : List.ofFn (highBytes f)=(List.ofFn f).drop 16 := by
    have eq := slice_ofFn f 16 16 (by decide)
    have length : ((List.ofFn f).drop 16).length=16 := by simp
    rw [slice,List.take_of_length_le (by omega)] at eq
    exact eq.symm
  obtain ⟨lo,hlo⟩ := qm31_exists (lowBytes f) (low.symm ▸ parts.1)
  obtain ⟨hi,hhi⟩ := qm31_exists (highBytes f) (high.symm ▸ parts.2)
  exact ⟨(lo,hi),by simp [decodeWideLE,hlo,hhi]⟩

theorem wide_exists (b : Bytes) (length : b.length=32) (checked : canonical b) :
    ∃ value, FoldedLeafCodec.decodeWide b=some value := by
  let f : Fin 32 → (Fin 256) := fun i => b[i.val]'(by omega)
  have same : List.ofFn f=b := by
    apply List.ext_getElem
    · simp [length]
    · intro i hi hj
      simp only [List.getElem_ofFn,f]
  obtain ⟨limbs,decoded⟩ := wideLE_exists f (same.symm ▸ checked)
  refine ⟨WideExactLimbCodec.pairExactEquiv limbs,?_⟩
  rw [← same]
  simp only [FoldedLeafCodec.decodeWide,ListFieldCodec.fixedBytes?_ofFn,Option.bind_some,decoded,Option.map_some]

#print axioms slice_ofFn
#print axioms word_bound
#print axioms qm31_exists
#print axioms wideLE_exists
#print axioms wide_exists
end AspisR1.PAln_FieldRead
