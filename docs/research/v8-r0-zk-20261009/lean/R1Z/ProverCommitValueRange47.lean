import R1Z.ProverCommitCompact43
import R1FoldedLeafCodec
import R1Z.ProverCommitCircleSampler22
/-! The mathematical producer range, kept separate from source arithmetic and
source-to-payload equality. No codec-success or source-image premise is added. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitValueRange47
open AspisV8R15.ExactTowerBase AspisWideTower
open AspisR1.RetainedFieldByteCodec AspisR1.StrictWideByteCodec
open AspisR1.WideExactLimbCodec
open ProverCommitCompact43
abbrev Q := QM31Exact
abbrev E := WideExact

def embed (q : Q) : E := algebraMap Q E q

def InQM (x : E) : Prop := ∃ q : Q, x=embed q

theorem zero_range : InQM 0 := ⟨0,map_zero _ |>.symm⟩
theorem one_range : InQM 1 := ⟨1,map_one _ |>.symm⟩
theorem embed_range (q : Q) : InQM (embed q) := ⟨q,rfl⟩
theorem add_range (x y : E) (hx : InQM x) (hy : InQM y) : InQM (x+y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a+b,(map_add _ _ _).symm⟩
theorem mul_range (x y : E) (hx : InQM x) (hy : InQM y) : InQM (x*y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a*b,(map_mul _ _ _).symm⟩
theorem sub_range (x y : E) (hx : InQM x) (hy : InQM y) : InQM (x-y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b,(map_sub _ _ _).symm⟩

/-- Literal two-coordinate image of the source's from_qm31 constructor. -/
theorem embed_coordinates (q : Q) : embed q = ⟨q,0⟩ := rfl

/-- Canonical low limbs and zero high limbs, without a codec-success premise. -/
theorem embedded_limbs (q : Q) :
    pairExactEquiv.symm (embed q) =
      (AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.symm q,
       AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.symm 0) := by
  apply pairExactEquiv.injective
  simp only [Equiv.apply_symm_apply]
  rfl

def bytes (x : E) : Cell := fun i =>
  UInt8.ofFin (encodeWideLE (pairExactEquiv.symm x) i)

theorem bytes_decode (x : E) :
    AspisR1.FoldedLeafCodec.decodeWide ((List.ofFn (bytes x)).map UInt8.toFin) = some x := by
  have h : (List.ofFn (bytes x)).map UInt8.toFin = AspisR1.FoldedLeafCodec.encodeWide x := by
    simp only [List.map_ofFn]
    rfl
  rw [h]
  exact AspisR1.FoldedLeafCodec.decodeWide_encode x

/-- A zero-QM31 canonical limb tuple is pointwise zero. -/
theorem zero_limbs : AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.symm (0 : Q) =
    fun _ => 0 := by
  apply AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv.injective
  simp only [Equiv.apply_symm_apply]
  rfl

theorem zero_bytes (i : Fin 16) : encodeQM31LE (fun _ => 0) i = 0 := by
  simp only [encodeQM31LE,encodeM31LE,encodeWordLE,m31AsRawWord]
  generalize h : ((finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm i).2 = j
  fin_cases j <;> rfl

theorem embedded_high_zero (q : Q) : highZero (bytes (embed q)) := by
  intro i
  have hi : (⟨16+i.val,by omega⟩ : Fin 32) = Fin.natAdd 16 i := by
    apply Fin.ext
    rfl
  rw [bytes,hi,embedded_limbs,encodeWideLE,Fin.append_right,zero_limbs,zero_bytes]
  rfl

theorem range_compact (x : E) (hx : InQM x) (out : ProverCommitPublish43.Bytes) :
    cell (bytes x) out = .ok (out ++ low (bytes x)) := by
  obtain ⟨q,rfl⟩ := hx
  exact (cell_ok _ _ _).mpr ⟨embedded_high_zero q,rfl⟩

#print axioms zero_range
#print axioms one_range
#print axioms embed_range
#print axioms add_range
#print axioms mul_range
#print axioms sub_range
#print axioms embed_coordinates
#print axioms embedded_limbs
#print axioms bytes_decode
#print axioms zero_limbs
#print axioms zero_bytes
#print axioms embedded_high_zero
#print axioms range_compact
end R1Z.ProverCommitValueRange47
