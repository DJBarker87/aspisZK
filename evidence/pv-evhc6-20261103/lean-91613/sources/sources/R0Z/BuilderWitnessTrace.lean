import R0Z.BuilderWitnessTree
import R0Z.WriterRefineAuxBlock
import R0Z.WriterRefinePathModel

/-! The witness-level Rust-copy builder, part 3: aux rows and the whole trace
(DESIGN-BUILDER-MODEL §12 (2)).

The path aux arrays (bits, current, left, right per level), the value triple
and the two occupancy records are computed from the records and the copy's
digests; `PathLifts`, `ValueLifts` and both `OccLifts` become theorems.  The
output occupancy inverse is the glue function `invR` (x^(p-2) mod p, the
value M31::inv returns); its lift is the field inverse given the named fact
`Nat.Prime 2147483647` (Fermat).  `copyCell W P c r` assembles the 29 x 1024
trace from the 57 chained copy blocks, the path block (rows 912..1007) and the
aux block (rows 1008..1023), columns 16..28 zero; `builder_witness_model`:
every component returns `ok` and every cell lifts to `buildModel pub (toModel W)`.
Not modelled: the Rust bank merge (rows 544..863 written into the late bank
and merged; `merge_model` covers the merge itself). -/
set_option autoImplicit false
noncomputable section

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result
open R0Z.BuilderModel

def arr24 {α : Type} (f : Fin 24 → α) : Array α 24#usize := ⟨List.ofFn f, by simp⟩

theorem arr24_get {α : Type} [Inhabited α] (f : Fin 24 → α) (i : Nat) (h : i < 24) :
    (arr24 f).val[i]! = f ⟨i, h⟩ := by
  show (List.ofFn f)[i]! = _
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  rfl

def levelPair (W : RustWitness) (P : RustPublic) (l : Fin 24) : Array U32 8#usize × Array U32 8#usize :=
  orderedR (okOr (treeCurR W P l.val) zero8) (W.sibs.val[l.val]!) (bitB W l.val)

def curArr (W : RustWitness) (P : RustPublic) : Array (Array U32 8#usize) 24#usize :=
  arr24 (fun l => okOr (treeCurR W P l.val) zero8)
def leftArr (W : RustWitness) (P : RustPublic) : Array (Array U32 8#usize) 24#usize :=
  arr24 (fun l => (levelPair W P l).1)
def rightArr (W : RustWitness) (P : RustPublic) : Array (Array U32 8#usize) 24#usize :=
  arr24 (fun l => (levelPair W P l).2)

def valuesArr (W : RustWitness) : Array U32 3#usize := ⟨[W.inputValue, W.outputValue, W.changeValue], by simp⟩

/-- x^(p-2) mod p as a u32 (glue for M31::inv in two_outputs). -/
def invR (x : U32) : U32 := ⟨BitVec.ofNat 32 (x.val ^ 2147483645 % 2147483647)⟩

def inRec (W : RustWitness) : R0WriterCopies.OccRecord :=
  ⟨W.pairOccupied, W.pairInverse, W.pairSecond, W.bits.val[0]!, true⟩

def outRec (W : RustWitness) (P : RustPublic) : R0WriterCopies.OccRecord :=
  match P.variant with
  | .privateTransfer =>
      ⟨1#u32, invR ((okOr (changeDR W P) zero8).val[7]!), okOr (changeDR W P) zero8, 0#u32, false⟩
  | .withdrawal => ⟨0#u32, 0#u32, zero8, 0#u32, false⟩

def pathR (W : RustWitness) (P : RustPublic) : Result (Array U32 1536#usize) :=
  R0WriterCopies.write_path_block W.bits (curArr W P) (leftArr W P) (rightArr W P)

def auxR (W : RustWitness) (P : RustPublic) : Result (Array U32 256#usize) :=
  R0WriterCopies.write_aux_block (valuesArr W) (inRec W) (outRec W P)

def blockR (W : RustWitness) (P : RustPublic) (h : Nat) : Array U32 256#usize :=
  okOr (RustWriterChain P.variant (rustChunks W P) h) (Array.repeat 256#usize 0#u32)

/-- **The assembled copy trace** (29 columns x 1024 rows of u32). -/
def copyCell (W : RustWitness) (P : RustPublic) (c : Fin 29) (r : Fin 1024) : U32 :=
  if c.val < 16 then
    if r.val < 912 then (blockR W P (r.val / 16)).val[(r.val % 16) * 16 + c.val]!
    else if r.val < 1008 then (okOr (pathR W P) (Array.repeat 1536#usize 0#u32)).val[(r.val - 912) * 16 + c.val]!
    else (okOr (auxR W P) (Array.repeat 256#usize 0#u32)).val[(r.val - 1008) * 16 + c.val]!
  else 0#u32

variable {K : Type} [Field K] [CharP K 0x7fffffff]

theorem invR_lift (hp : Nat.Prime 2147483647) (x : U32) :
    liftU (K := K) (invR x) = (liftU (K := K) x)⁻¹ := by
  have hv : (invR x).val = x.val ^ 2147483645 % 2147483647 := by
    show (BitVec.ofNat 32 _).toNat = _
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))
  unfold liftU
  rw [hv, R0Z.PoseidonRefine.cast_mod, Nat.cast_pow]
  haveI : Fact (Nat.Prime 2147483647) := ⟨hp⟩
  by_cases ha : ((x.val : Nat) : K) = 0
  · rw [ha, zero_pow (by norm_num), inv_zero]
  · have hz : ((x.val : ZMod 2147483647)) ≠ 0 := by
      intro hz
      apply ha
      rw [← map_natCast (ZMod.castHom (dvd_refl 2147483647) K) x.val, hz, map_zero]
    have h2 := congrArg (ZMod.castHom (dvd_refl 2147483647) K) (ZMod.pow_card_sub_one_eq_one hz)
    rw [map_pow, map_natCast, map_one] at h2
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact h2

section trace
variable (W : RustWitness) (P : RustPublic) (pub : R0P.Public K) (hP : PubCorr P pub) (hW : WitnessOk W)

include hP hW in
theorem rust_path_lifts : PathLifts (K := K) W.bits (curArr W P) (leftArr W P) (rightArr W P)
    (cellsOf pub (toModel W)) := by
  refine ⟨fun v => ?_, fun v i => ?_, fun v i => ?_, fun v i => ?_⟩
  · show liftU (W.bits.val[v.val]!) = dirK (decide ((W.bits.val[v.val]!).val ≠ 0))
    unfold dirK liftU
    rcases hW.bits v.val v.isLt with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  · obtain ⟨c, hc, hcl, -⟩ := treeCur_lift W P pub hP hW v.val (by omega)
    show liftU (((curArr W P).val[v.val]!).val[i.val]!) = treeCur _ _ v.val i
    rw [curArr, arr24_get _ _ v.isLt]
    dsimp only
    rw [hc, okOr_ok]
    exact hcl i
  · obtain ⟨c, hc, hcl, hcc⟩ := treeCur_lift W P pub hP hW v.val (by omega)
    have ol := ordered_lift c (W.sibs.val[v.val]!) _ (digK (K := K) (W.sibs.val[v.val]!)) (bitB W v.val)
      hcl (fun i => rfl) hcc (hW.sibs _ v.isLt)
    show liftU (((leftArr W P).val[v.val]!).val[i.val]!) = _
    rw [leftArr, arr24_get _ _ v.isLt]
    dsimp only [levelPair]
    rw [hc, okOr_ok]
    exact ol.1 i
  · obtain ⟨c, hc, hcl, hcc⟩ := treeCur_lift W P pub hP hW v.val (by omega)
    have ol := ordered_lift c (W.sibs.val[v.val]!) _ (digK (K := K) (W.sibs.val[v.val]!)) (bitB W v.val)
      hcl (fun i => rfl) hcc (hW.sibs _ v.isLt)
    show liftU (((rightArr W P).val[v.val]!).val[i.val]!) = _
    rw [rightArr, arr24_get _ _ v.isLt]
    dsimp only [levelPair]
    rw [hc, okOr_ok]
    exact ol.2.1 i

include hW in
theorem rust_value_lifts : ValueLifts (K := K) (valuesArr W) (cellsOf pub (toModel W)) := by
  have hv := hW.values
  refine ⟨fun i hi => ?_, fun i => ?_⟩
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact hv.1
    · exact hv.2.1
    · exact hv.2.2
  · obtain ⟨iv, hi⟩ := i
    have : iv = 0 ∨ iv = 1 ∨ iv = 2 := by omega
    rcases this with rfl | rfl | rfl
    · show W.inputValue.val % 2 ^ 30 = _; exact Nat.mod_eq_of_lt hv.1
    · show W.outputValue.val % 2 ^ 30 = _; exact Nat.mod_eq_of_lt hv.2.1
    · show W.changeValue.val % 2 ^ 30 = _; exact Nat.mod_eq_of_lt hv.2.2

include hW in
theorem rust_in_occ : OccLifts (K := K) (inRec W) (cellsOf pub (toModel W)).inOcc := by
  refine ⟨rfl, rfl, fun i => rfl, ?_⟩
  show liftU (W.bits.val[0]!) = dirK (decide ((W.bits.val[0]!).val ≠ 0))
  unfold dirK liftU
  rcases hW.bits 0 (by omega) with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

include hP hW in
theorem rust_out_occ (hp : Nat.Prime 2147483647) :
    OccLifts (K := K) (outRec W P) (cellsOf pub (toModel W)).outOcc := by
  show OccLifts (outRec W P) (outOccOf pub (toModel W))
  unfold outRec outOccOf
  rw [hP.variant]
  cases hv : pub.variant
  · obtain ⟨dc, hdc, hdcl, -⟩ := noteDigest_lift pub (toModel (K := K) W) (chunksOf W P)
      (chunks_sabs W P pub hP hW) 32 (nk 32 (by omega)) (zk _ 32 (by omega))
    replace hdc : changeDR W P = ok dc := hdc
    rw [hdc, okOr_ok]
    refine ⟨?_, ?_, hdcl, ?_⟩
    · show liftU (K := K) 1#u32 = 1; unfold liftU; simp
    · show liftU (K := K) (invR (dc.val[7]!)) = (changeDigest pub (toModel W) 7)⁻¹
      rw [invR_lift hp]
      exact congrArg (·⁻¹) (hdcl 7)
    · show (0 : K) = 0; rfl
  · refine ⟨?_, ?_, zero8_lift, ?_⟩
    · show liftU (K := K) 0#u32 = 0; unfold liftU; simp
    · show liftU (K := K) 0#u32 = 0; unfold liftU; simp
    · show (0 : K) = 0; rfl

include hP hW in
/-- **The witness-level copy builder equals the model.**  Every component of the
composition returns `ok`, and every cell of the assembled trace lifts to
`buildModel pub (toModel W)`. -/
theorem builder_witness_model (hp : Nat.Prime 2147483647) :
    (∀ h : Fin 57, ∃ b, RustWriterChain P.variant (rustChunks W P) h.val = ok b) ∧
    (∃ pb, pathR W P = ok pb) ∧ (∃ ab, auxR W P = ok ab) ∧
    ∀ (c : Fin 29) (r : Fin 1024), liftU (K := K) (copyCell W P c r) = buildModel pub (toModel W) c r := by
  obtain ⟨pb, hpb, hpbv⟩ := path_block_model W.bits (curArr W P) (leftArr W P) (rightArr W P)
    (cellsOf pub (toModel (K := K) W)) (rust_path_lifts W P pub hP hW)
  obtain ⟨ab, hab, habv⟩ := aux_block_model (valuesArr W) (inRec W) (outRec W P)
    (cellsOf pub (toModel (K := K) W)) (rust_value_lifts W pub hW) (rust_in_occ W pub hW)
    (rust_out_occ W P pub hP hW hp)
  refine ⟨fun h => ?_, ⟨pb, hpb⟩, ⟨ab, hab⟩, fun c r => ?_⟩
  · obtain ⟨b, hb, -⟩ := builder_witness_blocks W P pub hP hW h
    exact ⟨b, hb⟩
  have hr := r.isLt
  by_cases hc : c.val < 16
  · by_cases h912 : r.val < 912
    · obtain ⟨b, hb, hbv⟩ := builder_witness_blocks W P pub hP hW ⟨r.val / 16, by omega⟩
      have e : copyCell W P c r = b.val[(r.val % 16) * 16 + c.val]! := by
        unfold copyCell
        rw [if_pos hc, if_pos h912]
        show (okOr (RustWriterChain P.variant (rustChunks W P) (r.val / 16)) _).val[_]! = _
        rw [show (RustWriterChain P.variant (rustChunks W P) (r.val / 16)) = ok b from hb, okOr_ok]
      rw [e]
      have := hbv ⟨r.val % 16, Nat.mod_lt _ (by omega)⟩ ⟨c.val, hc⟩
      rw [this]
      congr 1
      exact Fin.ext (by simp; omega)
    · by_cases h1008 : r.val < 1008
      · have e : copyCell W P c r = pb.val[(r.val - 912) * 16 + c.val]! := by
          unfold copyCell
          rw [if_pos hc, if_neg h912, if_pos h1008, show pathR W P = ok pb from hpb, okOr_ok]
        rw [e, hpbv (r.val - 912) (by omega) ⟨c.val, hc⟩, buildModel,
          layout_aux _ c r hc (by omega), show 912 + (r.val - 912) = r.val by omega]
      · have e : copyCell W P c r = ab.val[(r.val - 1008) * 16 + c.val]! := by
          unfold copyCell
          rw [if_pos hc, if_neg h912, if_neg h1008, show auxR W P = ok ab from hab, okOr_ok]
        have := habv ⟨r.val - 1008, by omega⟩ ⟨c.val, hc⟩
        rw [e, this, buildModel, layout_aux _ c r hc (by omega)]
        dsimp only
        rw [show 1008 + (r.val - 1008) = r.val by omega]
  · have e : copyCell W P c r = 0#u32 := by unfold copyCell; rw [if_neg hc]
    rw [e, buildModel, layout_high _ c r (by omega)]
    unfold liftU; simp

end trace

#print axioms R0Z.WriterRefine.invR_lift
#print axioms R0Z.WriterRefine.rust_path_lifts
#print axioms R0Z.WriterRefine.rust_out_occ
#print axioms R0Z.WriterRefine.builder_witness_model
end R0Z.WriterRefine
