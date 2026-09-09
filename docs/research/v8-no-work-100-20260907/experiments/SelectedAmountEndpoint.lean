import SelectedSparseMle
import SelectedTransferPositive

/-! Deterministic selected-transfer amount endpoint. Exact seven singleton
copy aliases, source-shaped range/conservation expressions, and the SAME
table's sparse-read positive pack imply strict raw decoded amounts. The
premises are individual residuals, NOT verifier acceptance or valid-witness
assumptions. The source constant/loop model is not Rust-machine translation.
-/
set_option autoImplicit false
namespace AspisV8.SelectedAmountEndpoint
open scoped BigOperators
open AspisFormal.ArithmetizationCore
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedPaymentRecovery
open AspisV8.SelectedTransferPositive
open AspisV8.SelectedSparseMle

abbrev Cell := Nat × Nat

/-- Literal COPY_LINKS entries 11..17, tags1124073483..3489, reduced to
their singleton tuple coordinates. Patterns6/7/8/9 read columns0/10/1/2.
All offsets are zero. The transfer-only recipient edge has weight ONE in
this explicitly transfer-only slice. Slots matter to the probabilistic
copy protocol, not to this individual tuple-difference predicate. -/
def aliasProducer : Fin 7 → Cell :=
  ![(44,0),(460,0),(508,0),(1008,10),(1010,10),(1012,10),(1014,2)]
def aliasConsumer : Fin 7 → Cell :=
  ![(1008,10),(1010,10),(1012,10),(1014,0),(1014,1),(1015,1),(1015,0)]
def singletonTuple (t : Table) (cell : Cell) (lane : Fin 16) : F :=
  if lane.val=0 then t cell.1 cell.2 else 0
def aliasResidual (t : Table) (edge : Fin 7) (lane : Fin 16) : F :=
  1*(singletonTuple t (aliasProducer edge) lane-
     singletonTuple t (aliasConsumer edge) lane)
def AliasResiduals (t : Table) : Prop := ∀ edge lane, aliasResidual t edge lane=0

theorem alias_lane_zero (t : Table) (h : AliasResiduals t) (edge : Fin 7) :
    t (aliasProducer edge).1 (aliasProducer edge).2-
      t (aliasConsumer edge).1 (aliasConsumer edge).2=0 := by
  simpa only [aliasResidual,singletonTuple,Fin.val_zero,ite_true,one_mul] using h edge 0

/-- Literal `view[..n].iter().rev().fold(seed, acc+acc+bit)` helper. -/
def sourceHorner (f : Nat → F) (n : Nat) (seed : F) : F :=
  ((List.range n).reverse).foldl (fun acc i=>acc+acc+f i) seed

theorem sourceHorner_succ (f : Nat → F) (n : Nat) (seed : F) :
    sourceHorner f (n+1) seed=sourceHorner f n (seed+seed+f n) := by
  simp only [sourceHorner,List.range_succ,List.reverse_append,List.reverse_singleton,
    List.singleton_append,List.foldl_cons]

theorem sourceHorner_sum (f : Nat → F) (n : Nat) (seed : F) :
    sourceHorner f n seed=(∑ i ∈ Finset.range n,f i*(2:F)^i)+seed*(2:F)^n := by
  induction n generalizing seed with
  | zero => simp [sourceHorner]
  | succ n ih =>
    rw [sourceHorner_succ,ih,Finset.sum_range_succ,pow_succ]
    ring

def blockRead (t : Table) (which : Fin 3) (limb : Fin 3) (i : Nat) : F :=
  bitValue t which (limbBit limb ⟨i%10,by omega⟩)
def sourceBlock (t : Table) (which : Fin 3) (limb : Fin 3) : F :=
  sourceHorner (blockRead t which limb) 9 (blockRead t which limb 9)

theorem sourceBlock_sum (t : Table) (which : Fin 3) (limb : Fin 3) :
    sourceBlock t which limb=
      ∑ bit : Fin 10,bitValue t which (limbBit limb bit)*(2:F)^bit.val := by
  rw [sourceBlock,sourceHorner_sum]
  have hs : (∑ i ∈ Finset.range 9,blockRead t which limb i*(2:F)^i)+
      blockRead t which limb 9*(2:F)^9=
      ∑ i ∈ Finset.range 10,blockRead t which limb i*(2:F)^i := by
    exact (Finset.sum_range_succ (fun i=>blockRead t which limb i*(2:F)^i) 9).symm
  rw [hs,Finset.sum_range]
  apply Finset.sum_congr rfl
  intro bit _
  simp only [blockRead,Nat.mod_eq_of_lt bit.isLt]

/-- Literal reverse-Horner ten-bit blocks, with scale1,2^10,2^20.
The underlying bit cells are the selected current/successor/XOR12 rows. -/
def compiledReconstruction (t : Table) (which : Fin 3) : F :=
  ∑ limb : Fin 3,sourceBlock t which limb*(2:F)^(10*limb.val)

theorem compiledReconstruction_eq (t : Table) (which : Fin 3) :
    compiledReconstruction t which=
      ∑ bit : Fin 30,bitValue t which bit*(2:F)^bit.val := by
  rw [split_thirty]
  unfold compiledReconstruction
  apply Finset.sum_congr rfl
  intro limb _
  rw [sourceBlock_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro bit _
  simp only [limbBit,pow_add]
  ring

/-- This contains the six actual auxiliary zeros, not the relation-free
host-padding class. The next implication only needs a sufficient subset;
none of these source checks is deleted from this predicate. -/
structure CompiledAmountResiduals (t : Table) : Prop where
  boolean : ∀ which bit,(bitValue t which bit)^2-bitValue t which bit=0
  recomposition : ∀ which,t (valueBase which) 10-compiledReconstruction t which=0
  auxiliary : ∀ which,t (valueBase which+1) 10=0 ∧
    t (Nat.xor (valueBase which) 12) 10=0
  aliases : AliasResiduals t
  first : t 1014 0-t 1014 1-t 1014 2=0
  second : t 1015 0-t 1015 1=0

theorem compiled_value_residuals (t : Table) (h : CompiledAmountResiduals t) :
    ValueResiduals t := by
  refine ⟨?_,?_,?_⟩
  · intro which bit
    have hb:=h.boolean which bit
    linear_combination hb
  · intro which
    simpa only [compiledReconstruction_eq] using h.recomposition which
  · intro which
    fin_cases which
    · exact alias_lane_zero t h.aliases 0
    · exact alias_lane_zero t h.aliases 1
    · exact alias_lane_zero t h.aliases 2

/-- In particular, the first compiled conservation polynomial is the
negative of the older diagnostic predicate; equality of zeros is proved. -/
theorem compiled_conservation_residuals (t : Table) (h : CompiledAmountResiduals t) :
    ConservationResiduals t := by
  refine ⟨alias_lane_zero t h.aliases 3,alias_lane_zero t h.aliases 4,
    alias_lane_zero t h.aliases 5,alias_lane_zero t h.aliases 6,?_,h.second⟩
  linear_combination -h.first

/-- Exact field embedding used to create the semantic QM31 message tables.
Both base moduli definitionally are 2^31-1; this is not a subfield premise. -/
def liftedColumn (t : Table) (col : Nat) : List QM31Exact :=
  List.ofFn (fun row : Fin 1024=>liftBase (t row.val col))

theorem liftedColumn_length (t : Table) (col : Nat) :
    (liftedColumn t col).length=1024 := List.length_ofFn

theorem liftedColumn_read (t : Table) (col row : Nat) (hr : row<1024) :
    (liftedColumn t col).getD row 0=liftBase (t row col) := by
  have h : row<(liftedColumn t col).length := by rw [liftedColumn_length]; exact hr
  rw [List.getD_eq_getElem _ _ h]
  simp only [liftedColumn,List.getElem_ofFn]

theorem liftBase_injective : Function.Injective liftBase := by
  intro x y h
  exact congrArg (fun z : QM31Exact=>z.re.re) h

theorem liftBase_product_one (a b u : F) :
    liftBase a*liftBase b*liftBase u=1 ↔ a*b*u=1 := by
  rw [←liftBase_mul,←liftBase_mul,←liftBase_one]
  exact liftBase_injective.eq_iff

/-- Column1 supplies both amount reads and column3 the reserved inverse;
their entire 1024-entry message lists are constructed from the same table.
No equality between independently supplied tables is a premise. -/
def tablePositivePack (t : Table) (publicAsset : QM31Exact) : Option QM31Exact :=
  currentPositivePack (liftedColumn t 1) (liftedColumn t 3) publicAsset

theorem table_pack_iff_residual (t : Table) (publicAsset : QM31Exact) :
    tablePositivePack t publicAsset=some 0 ↔ ProductInverseResidual t := by
  rw [tablePositivePack,current_positive_pack_binding _ _ _
    (liftedColumn_length t 1) (liftedColumn_length t 3),
    liftedColumn_read _ _ _ (by decide),liftedColumn_read _ _ _ (by decide),
    liftedColumn_read _ _ _ (by decide),liftBase_product_one]
  exact sub_eq_zero.symm

/-- The source copy chain is derived from residuals, not supplied as the
desired equality between decoded note amounts and helper rows. -/
theorem decoded_source_links (t : Table) (h : CompiledAmountResiduals t) :
    sourceValue t 1=t 1014 1 ∧ sourceValue t 2=t 1015 1 := by
  have recipientSource:=sub_eq_zero.mp (alias_lane_zero t h.aliases 1)
  have recipientTarget:=sub_eq_zero.mp (alias_lane_zero t h.aliases 4)
  have changeSource:=sub_eq_zero.mp (alias_lane_zero t h.aliases 2)
  have changeTarget:=sub_eq_zero.mp (alias_lane_zero t h.aliases 5)
  exact ⟨recipientSource.trans recipientTarget,changeSource.trans changeTarget⟩

/-- A genuinely connected deterministic endpoint: source-shaped residuals
and the modeled sparse-evaluated positive pack imply strict decoded amounts,
natural conservation and checked_add safety. No valid witness is assumed. -/
theorem strict_decoded_amounts (t : Table) (publicAsset : QM31Exact)
    (h : CompiledAmountResiduals t) (hp : tablePositivePack t publicAsset=some 0) :
    (∀ which,0<decodedValue t which ∧ decodedValue t which<2^30) ∧
    decodedValue t 0=decodedValue t 1+decodedValue t 2 ∧
    decodedValue t 1+decodedValue t 2<2^32 := by
  exact selected_strict_amounts t (compiled_value_residuals t h)
    (compiled_conservation_residuals t h) ((table_pack_iff_residual t publicAsset).mp hp)

/-- Same row/column convention as recovered_witness::decode. Canonicality
is needed at the three raw amounts, not fabricated from their field residues. -/
theorem strict_raw_amounts (raw : Nat → Nat → Nat) (publicAsset : QM31Exact)
    (canonical : ∀ which,raw (sourceRow which) 0<p)
    (h : CompiledAmountResiduals (fieldTable raw))
    (hp : tablePositivePack (fieldTable raw) publicAsset=some 0) :
    (∀ which,0<raw (sourceRow which) 0 ∧ raw (sourceRow which) 0<2^30) ∧
    raw 44 0=raw 460 0+raw 508 0 ∧ raw 460 0+raw 508 0<2^32 := by
  have valueExact : ∀ which,decodedValue (fieldTable raw) which=raw (sourceRow which) 0 := by
    intro which
    exact raw_decoder_representative _ (canonical which)
  obtain ⟨bounds,balance,total⟩:=strict_decoded_amounts (fieldTable raw) publicAsset h hp
  refine ⟨?_,?_,?_⟩
  · intro which
    simpa only [valueExact] using bounds which
  · rw [valueExact 0,valueExact 1,valueExact 2] at balance
    exact balance
  · rw [valueExact 1,valueExact 2] at total
    exact total

#print axioms sourceHorner_sum
#print axioms sourceBlock_sum
#print axioms compiledReconstruction_eq
#print axioms compiled_value_residuals
#print axioms compiled_conservation_residuals
#print axioms liftedColumn_read
#print axioms liftBase_product_one
#print axioms table_pack_iff_residual
#print axioms decoded_source_links
#print axioms strict_decoded_amounts
#print axioms strict_raw_amounts
end AspisV8.SelectedAmountEndpoint
