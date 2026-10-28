import JHu_FrontierRun
import NDO_JHu_FixtureDigests
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
namespace AspisR1.JHu_FrontierFixture
open Aeneas Aeneas.Std Result
local instance : Inhabited (Array U32 (Usize.ofNatCore 8 (8#usize).hBounds)) :=
  ⟨Array.repeat 8#usize 0#u32⟩

/-- Each read uses its independently checked digest field, with symbolic address transport. -/
theorem reads : ∀ (n : Nat), n<20 → ∀ addr : Usize, addr.val=48+32*n →
    NCV_Reference.digest JHu_FixtureDigests.tree addr=
      ok (.Ok (NCV_ArrayFrame.coord JFt_SnapshotValue.value.frontier n)) := by
  intro n hn
  interval_cases n
  · intro addr ha
    have same : addr=48#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 48#usize=ok (.Ok JFt_Digest02.value)
    exact JHu_FixtureDigests.frontier_00
  · intro addr ha
    have same : addr=80#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 80#usize=ok (.Ok JFt_Digest03.value)
    exact JHu_FixtureDigests.frontier_01
  · intro addr ha
    have same : addr=112#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 112#usize=ok (.Ok JFt_Digest04.value)
    exact JHu_FixtureDigests.frontier_02
  · intro addr ha
    have same : addr=144#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 144#usize=ok (.Ok JFt_Digest05.value)
    exact JHu_FixtureDigests.frontier_03
  · intro addr ha
    have same : addr=176#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 176#usize=ok (.Ok JFt_Digest06.value)
    exact JHu_FixtureDigests.frontier_04
  · intro addr ha
    have same : addr=208#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 208#usize=ok (.Ok JFt_Digest07.value)
    exact JHu_FixtureDigests.frontier_05
  · intro addr ha
    have same : addr=240#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 240#usize=ok (.Ok JFt_Digest08.value)
    exact JHu_FixtureDigests.frontier_06
  · intro addr ha
    have same : addr=272#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 272#usize=ok (.Ok JFt_Digest09.value)
    exact JHu_FixtureDigests.frontier_07
  · intro addr ha
    have same : addr=304#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 304#usize=ok (.Ok JFt_Digest10.value)
    exact JHu_FixtureDigests.frontier_08
  · intro addr ha
    have same : addr=336#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 336#usize=ok (.Ok JFt_Digest11.value)
    exact JHu_FixtureDigests.frontier_09
  · intro addr ha
    have same : addr=368#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 368#usize=ok (.Ok JFt_Digest12.value)
    exact JHu_FixtureDigests.frontier_10
  · intro addr ha
    have same : addr=400#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 400#usize=ok (.Ok JFt_Digest13.value)
    exact JHu_FixtureDigests.frontier_11
  · intro addr ha
    have same : addr=432#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 432#usize=ok (.Ok JFt_Digest14.value)
    exact JHu_FixtureDigests.frontier_12
  · intro addr ha
    have same : addr=464#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 464#usize=ok (.Ok JFt_Digest15.value)
    exact JHu_FixtureDigests.frontier_13
  · intro addr ha
    have same : addr=496#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 496#usize=ok (.Ok JFt_Digest16.value)
    exact JHu_FixtureDigests.frontier_14
  · intro addr ha
    have same : addr=528#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 528#usize=ok (.Ok JFt_Digest17.value)
    exact JHu_FixtureDigests.frontier_15
  · intro addr ha
    have same : addr=560#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 560#usize=ok (.Ok JFt_Digest18.value)
    exact JHu_FixtureDigests.frontier_16
  · intro addr ha
    have same : addr=592#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 592#usize=ok (.Ok JFt_Digest19.value)
    exact JHu_FixtureDigests.frontier_17
  · intro addr ha
    have same : addr=624#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 624#usize=ok (.Ok JFt_Digest20.value)
    exact JHu_FixtureDigests.frontier_18
  · intro addr ha
    have same : addr=656#usize := UScalar.eq_of_val_eq ha
    subst addr
    change NCV_Reference.digest JHu_FixtureDigests.tree 656#usize=ok (.Ok JFt_Digest21.value)
    exact JHu_FixtureDigests.frontier_19
#print axioms reads

/-- Twenty scalar occupancy cases, selecting only the corresponding eight-limb empty row. -/
theorem bits : ∀ (n : Nat), n<20 → ∀ i : Usize, i.val=n → ∃ tag : U64,
    13#u64 >>> i=ok tag ∧ (tag &&& 1#u64=0#u64 →
      NCV_ArrayFrame.coord JFt_SnapshotValue.value.frontier n=NCV_ArrayFrame.coord NCV_Reference.EMPTY n) := by
  intro n hn
  interval_cases n
  · intro i hi
    have same : i=0#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨13#u64,by rfl,?_⟩
    intro h
    have no : ¬(13#u64 &&& 1#u64=0#u64) := by decide
    exact False.elim (no h)
  · intro i hi
    have same : i=1#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨6#u64,by rfl,?_⟩
    intro _
    change JFt_Digest03.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 1
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest03.value,Array.make]
  · intro i hi
    have same : i=2#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨3#u64,by rfl,?_⟩
    intro h
    have no : ¬(3#u64 &&& 1#u64=0#u64) := by decide
    exact False.elim (no h)
  · intro i hi
    have same : i=3#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨1#u64,by rfl,?_⟩
    intro h
    have no : ¬(1#u64 &&& 1#u64=0#u64) := by decide
    exact False.elim (no h)
  · intro i hi
    have same : i=4#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest06.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 4
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest06.value,Array.make]
  · intro i hi
    have same : i=5#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest07.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 5
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest07.value,Array.make]
  · intro i hi
    have same : i=6#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest08.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 6
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest08.value,Array.make]
  · intro i hi
    have same : i=7#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest09.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 7
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest09.value,Array.make]
  · intro i hi
    have same : i=8#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest10.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 8
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest10.value,Array.make]
  · intro i hi
    have same : i=9#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest11.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 9
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest11.value,Array.make]
  · intro i hi
    have same : i=10#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest12.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 10
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest12.value,Array.make]
  · intro i hi
    have same : i=11#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest13.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 11
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest13.value,Array.make]
  · intro i hi
    have same : i=12#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest14.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 12
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest14.value,Array.make]
  · intro i hi
    have same : i=13#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest15.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 13
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest15.value,Array.make]
  · intro i hi
    have same : i=14#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest16.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 14
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest16.value,Array.make]
  · intro i hi
    have same : i=15#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest17.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 15
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest17.value,Array.make]
  · intro i hi
    have same : i=16#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest18.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 16
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest18.value,Array.make]
  · intro i hi
    have same : i=17#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest19.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 17
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest19.value,Array.make]
  · intro i hi
    have same : i=18#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest20.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 18
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest20.value,Array.make]
  · intro i hi
    have same : i=19#usize := UScalar.eq_of_val_eq hi
    subst i
    refine ⟨0#u64,by rfl,?_⟩
    intro _
    change JFt_Digest21.value=NCV_ArrayFrame.coord NCV_Reference.EMPTY 19
    simp only [NCV_Reference.EMPTY,NCV_ArrayFrame.coord,List.getElem?_cons_succ,
      List.getElem?_cons_zero,Option.getD_some,JFt_Digest21.value,Array.make]
#print axioms bits

theorem source : NCV_Reference.decode_frontier JHu_FixtureDigests.tree 13#u64=
    ok (.Ok JFt_SnapshotValue.value.frontier) := by
  apply JHu_FrontierRun.source
  · intro i addr hi ha
    exact reads i.val hi addr ha
  · intro i hi
    exact bits i.val hi i rfl
#print axioms source
end AspisR1.JHu_FrontierFixture
