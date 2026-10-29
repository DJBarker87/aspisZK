import R0Z.BuilderWitnessMerged
import AspisV8R15.ExactTowerBase

/-! (d) The Wspend⁺ → RustWitness / RustPublic / ModelWitness map, T1–T3 (DESIGN-BUILD-
INTEGRATION §10.4; DESIGN-BUILDER-MODEL §12.6).  Stated on ModelWitness-shaped records over the
concrete field `M31Exact`, so this module needs no spend-path module (SpendRelation waits for
the X/R1X decision; T4 composes there).

* `toRust`, `toRustPub`: canonical u32 words of the M31 coordinates (`ZMod.val`), bits 0/1 from
  the path directions, the empty-root table as words;
* `ι := ZMod.castHom`: the carrier map into any `K` of characteristic `p`;
* T1 `toModel_toRust`: `toModel (toRust w) = mapW ι w`;
* T2 `witnessOk_toRust`: `WitnessOk (toRust w)`;
* T3 `pubCorr_toRustPub`: `PubCorr (toRustPub pub) (mapPub ι pub)`. -/
set_option autoImplicit false
noncomputable section
namespace R1J.SpendWitnessMap
open Aeneas Aeneas.Std Result
open R0Z.BuilderModel R0Z.WriterRefine

abbrev F := AspisV8R15.ExactTowerBase.M31Exact

instance : NeZero AspisV8R15.ExactTowerBase.P := ⟨by norm_num [AspisV8R15.ExactTowerBase.P]⟩

theorem val_lt_p (x : F) : x.val < 2147483647 := ZMod.val_lt x

theorem lt_u32 {n : ℕ} (h : n < 2147483647) : n < 2 ^ UScalarTy.U32.numBits := by
  have h32 : (2 : ℕ) ^ UScalarTy.U32.numBits = 4294967296 := rfl
  omega

/-! ### Words and arrays -/

def w32 (x : F) : U32 := UScalar.ofNatCore x.val (lt_u32 (val_lt_p x))

theorem w32_val (x : F) : (w32 x).val = x.val := UScalar.ofNatCore_val_eq _

def v32 (v : Fin (2 ^ 30)) : U32 :=
  UScalar.ofNatCore v.val (lt_u32 (lt_trans v.isLt (by norm_num)))

theorem v32_val (v : Fin (2 ^ 30)) : (v32 v).val = v.val := UScalar.ofNatCore_val_eq _

def d32 (d : Fin 8 → F) : Array U32 8#usize := arr8 (fun i => w32 (d i))

def arr24 {α : Type} (f : Fin 24 → α) : Array α 24#usize := ⟨List.ofFn f, by simp⟩
def arr20 {α : Type} (f : Fin 20 → α) : Array α 20#usize := ⟨List.ofFn f, by simp⟩

theorem arr24_get {α : Type} [Inhabited α] (f : Fin 24 → α) (l : ℕ) (h : l < 24) :
    (arr24 f).val[l]! = f ⟨l, h⟩ := by
  show (List.ofFn f)[l]! = _
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  rfl

theorem arr20_get {α : Type} [Inhabited α] (f : Fin 20 → α) (l : ℕ) (h : l < 20) :
    (arr20 f).val[l]! = f ⟨l, h⟩ := by
  show (List.ofFn f)[l]! = _
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  rfl

theorem arr8_getF (f : Fin 8 → U32) (i : Fin 8) : (arr8 f).val[i.val]! = f i := by
  rw [arr8_get f i.val i.isLt]

theorem arr24_getF {α : Type} [Inhabited α] (f : Fin 24 → α) (l : Fin 24) :
    (arr24 f).val[l.val]! = f l := by
  rw [arr24_get f l.val l.isLt]

theorem arr20_getF {α : Type} [Inhabited α] (f : Fin 20 → α) (l : Fin 20) :
    (arr20 f).val[l.val]! = f l := by
  rw [arr20_get f l.val l.isLt]

theorem d32_canon (d : Fin 8 → F) : Canon8 (d32 d) := by
  intro i hi
  rw [d32, arr8_get _ i hi, w32_val]
  exact val_lt_p _

/-! ### The carrier map and the model-side images -/

variable {K : Type} [Field K] [CharP K 2147483647]

def ι : F →+* K := ZMod.castHom (dvd_refl _) K

theorem ι_apply (x : F) : (ι : F →+* K) x = ((x.val : ℕ) : K) := by
  rw [ι, ZMod.castHom_apply, ZMod.cast_eq_val]

theorem liftU_w32 (x : F) : liftU (K := K) (w32 x) = (ι : F →+* K) x := by
  rw [liftU, w32_val, ι_apply]

theorem digK_d32 (d : Fin 8 → F) : digK (K := K) (d32 d) = fun i => (ι : F →+* K) (d i) := by
  funext i
  rw [digK, d32, arr8_getF, liftU_w32]

theorem val30_v32 (v : Fin (2 ^ 30)) : val30 (v32 v) = v := by
  apply Fin.ext
  simp only [val30, v32_val]
  exact Nat.mod_eq_of_lt v.isLt

def mapW (w : ModelWitness F) : ModelWitness K where
  inputValue := w.inputValue
  outputValue := w.outputValue
  changeValue := w.changeValue
  sk := fun i => (ι : F →+* K) (w.sk i)
  salt := fun i => (ι : F →+* K) (w.salt i)
  path := fun l => ((w.path l).1, fun i => (ι : F →+* K) ((w.path l).2 i))
  pairFirst := fun i => (ι : F →+* K) (w.pairFirst i)
  pairOccupied := (ι : F →+* K) w.pairOccupied
  pairSecond := fun i => (ι : F →+* K) (w.pairSecond i)
  pairInverse := (ι : F →+* K) w.pairInverse
  recipientOwner := fun i => (ι : F →+* K) (w.recipientOwner i)
  recipientSalt := fun i => (ι : F →+* K) (w.recipientSalt i)
  changeOwner := fun i => (ι : F →+* K) (w.changeOwner i)
  changeSalt := fun i => (ι : F →+* K) (w.changeSalt i)

def mapPub (pub : R0P.Public F) : R0P.Public K where
  variant := pub.variant
  anchor := fun i => (ι : F →+* K) (pub.anchor i)
  nullifier := fun i => (ι : F →+* K) (pub.nullifier i)
  assetId := (ι : F →+* K) pub.assetId
  recipient := pub.recipient.map (fun d i => (ι : F →+* K) (d i))
  change := fun i => (ι : F →+* K) (pub.change i)
  withdrawalAmount := pub.withdrawalAmount.map (ι : F →+* K)
  nextPairIndex := pub.nextPairIndex
  snapshotFrontier := fun l i => (ι : F →+* K) (pub.snapshotFrontier l i)
  nextRoot := fun i => (ι : F →+* K) (pub.nextRoot i)
  nextFrontier := fun l i => (ι : F →+* K) (pub.nextFrontier l i)

/-! ### The Rust records -/

def toRust (w : ModelWitness F) : RustWitness where
  inputValue := v32 w.inputValue
  outputValue := v32 w.outputValue
  changeValue := v32 w.changeValue
  sk := d32 w.sk
  salt := d32 w.salt
  bits := arr24 (fun l => if (w.path l).1 then 1#u32 else 0#u32)
  sibs := arr24 (fun l => d32 (w.path l).2)
  pairFirst := d32 w.pairFirst
  pairOccupied := w32 w.pairOccupied
  pairSecond := d32 w.pairSecond
  pairInverse := w32 w.pairInverse
  recipientOwner := d32 w.recipientOwner
  recipientSalt := d32 w.recipientSalt
  changeOwner := d32 w.changeOwner
  changeSalt := d32 w.changeSalt

/-- The pair_empty_roots table is canonical (each word below `p`). -/
theorem emptyRoot_lt : ∀ (l : Fin 21) (i : Fin 8), R0P.emptyRootsNat l i < 2147483647 := by
  unfold R0P.emptyRootsNat
  decide

def emptyWord (l : Fin 20) (i : Fin 8) : U32 :=
  UScalar.ofNatCore (R0P.emptyRootsNat l.castSucc i) (lt_u32 (emptyRoot_lt _ _))

def toRustPub (pub : R0P.Public F) : RustPublic where
  variant := pub.variant
  asset := w32 pub.assetId
  nextPairIndex := pub.nextPairIndex
  frontier := arr20 (fun l => d32 (pub.snapshotFrontier l))
  empty := arr20 (fun l => arr8 (emptyWord l))

/-! ### T1-T3 -/

/-- T1: the named witness map of the privacy builder, applied to the Rust record of an
M31 witness, is that witness carried into `K`. -/
theorem toModel_toRust (w : ModelWitness F) : toModel (K := K) (toRust w) = mapW w := by
  unfold toModel toRust mapW
  congr 1
  all_goals first
    | exact val30_v32 _
    | exact digK_d32 _
    | exact liftU_w32 _
    | skip
  funext l
  simp only [arr24_getF, digK_d32]
  generalize w.path l = p
  obtain ⟨b, d⟩ := p
  cases b <;> exact Prod.ext (by first | rfl | simp) rfl

/-- T2: the Rust record of an M31 witness satisfies the builder's range facts. -/
theorem witnessOk_toRust (w : ModelWitness F) : WitnessOk (toRust w) where
  values := ⟨by show (v32 w.inputValue).val < _; rw [v32_val]; exact w.inputValue.isLt,
    by show (v32 w.outputValue).val < _; rw [v32_val]; exact w.outputValue.isLt,
    by show (v32 w.changeValue).val < _; rw [v32_val]; exact w.changeValue.isLt⟩
  bits := by
    intro l hl
    show ((arr24 (fun l => if (w.path l).1 then 1#u32 else 0#u32)).val[l]!).val = 0 ∨
      ((arr24 (fun l => if (w.path l).1 then 1#u32 else 0#u32)).val[l]!).val = 1
    rw [arr24_get _ l hl]
    cases (w.path ⟨l, hl⟩).1
    · exact Or.inl rfl
    · exact Or.inr rfl
  sibs := by
    intro l hl
    show Canon8 ((arr24 (fun l => d32 (w.path l).2)).val[l]!)
    rw [arr24_get _ l hl]
    exact d32_canon (w.path ⟨l, hl⟩).2

/-- T3: the public-input correspondences for the Rust public record of an M31 statement. -/
theorem pubCorr_toRustPub (pub : R0P.Public F) : PubCorr (toRustPub pub) (mapPub (K := K) pub) where
  variant := rfl
  asset := liftU_w32 _
  next := rfl
  frontier := by
    intro l i
    show liftU (((arr20 (fun l => d32 (pub.snapshotFrontier l))).val[l.val]!).val[i.val]!) = _
    simp only [arr20_getF, d32, arr8_getF, liftU_w32]
    rfl
  empty := by
    intro l i
    show liftU (((arr20 (fun l => arr8 (emptyWord l))).val[l.val]!).val[i.val]!) = _
    simp only [arr20_getF, arr8_getF]
    rw [liftU, emptyWord, UScalar.ofNatCore_val_eq]
    rfl
  frontierCanon := by
    intro l
    show Canon8 ((arr20 (fun l => d32 (pub.snapshotFrontier l))).val[l.val]!)
    rw [arr20_getF]
    exact d32_canon _
  emptyCanon := by
    intro l i hi
    show ((((arr20 (fun l => arr8 (emptyWord l))).val[l.val]!)).val[i]!).val < 2147483647
    rw [arr20_getF, arr8_get _ i hi, emptyWord, UScalar.ofNatCore_val_eq]
    exact emptyRoot_lt _ _

end R1J.SpendWitnessMap

#print axioms R1J.SpendWitnessMap.emptyRoot_lt
#print axioms R1J.SpendWitnessMap.toModel_toRust
#print axioms R1J.SpendWitnessMap.witnessOk_toRust
#print axioms R1J.SpendWitnessMap.pubCorr_toRustPub
