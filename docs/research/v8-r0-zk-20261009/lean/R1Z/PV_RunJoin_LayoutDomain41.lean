import R1Z.PV_RunJoin_RowShapes41
import R1Z.PV_RunJoin_SemanticComplete40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LayoutDomain41
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_SemanticDomain40
variable [ExternalTypes]

/-- Fixed source row layout. The high-half obligations below must still be
proved for the caller's bytes; they contain no codec Result or model equation. -/
theorem domain (ops : ExternalFuns) (logical : Slice U8)
    (length : logical.length=13831)
    (h14 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 139).take 32))
    (h15 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 176).take 896))
    (h16 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 1077).take 896))
    (h17 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 1978).take 896))
    (h18 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 2879).take 896))
    (h19 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 3780).take 896))
    (h20 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 4681).take 896))
    (h21 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 5582).take 896))
    (h22 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 6483).take 896))
    (h23 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 7384).take 896))
    (h24 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 8285).take 896))
    (h25 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 9186).take 3712))
    (h26 : PV_RunJoin_HighDomain40.HighZero ((logical.val.drop 12903).take 928))
    : ∃ records, Domain ops logical 27#u8 32#usize 0#u8 records := by
  have last : Domain ops logical 27#u8 13831#usize 27#u8 [] :=
    .nil _ _ (by decide) (by apply UScalar.eq_of_val_eq; change 13831=logical.length;exact length.symm)
  have d26 : ∃ records, Domain ops logical 27#u8 12898#usize 26#u8 records := by
    let records := ([] : List (List U8))
    have ht := last
    exact ⟨_, .compact 12898#usize 928#usize 26#u8 5#u8 29 records
      (by decide) (PV_RunJoin_RowShapes41.row26 ops) (by decide) (by rfl)
      (by change 13831≤logical.length;omega) h26 (by
        have ha : after 12898#usize 928#usize=13831#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 12898#usize 5#usize 12903#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 12903#usize 928#usize 13831#usize rfl]
        have hr : U8.wrapping_add 26#u8 1#u8=27#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d25 : ∃ records, Domain ops logical 27#u8 9181#usize 25#u8 records := by
    obtain ⟨records,ht⟩ := d26
    exact ⟨_, .compact 9181#usize 3712#usize 25#u8 4#u8 116 records
      (by decide) (PV_RunJoin_RowShapes41.row25 ops) (by decide) (by rfl)
      (by change 12898≤logical.length;omega) h25 (by
        have ha : after 9181#usize 3712#usize=12898#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 9181#usize 5#usize 9186#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 9186#usize 3712#usize 12898#usize rfl]
        have hr : U8.wrapping_add 25#u8 1#u8=26#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d24 : ∃ records, Domain ops logical 27#u8 8280#usize 24#u8 records := by
    obtain ⟨records,ht⟩ := d25
    exact ⟨_, .compact 8280#usize 896#usize 24#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row24 ops) (by decide) (by rfl)
      (by change 9181≤logical.length;omega) h24 (by
        have ha : after 8280#usize 896#usize=9181#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 8280#usize 5#usize 8285#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 8285#usize 896#usize 9181#usize rfl]
        have hr : U8.wrapping_add 24#u8 1#u8=25#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d23 : ∃ records, Domain ops logical 27#u8 7379#usize 23#u8 records := by
    obtain ⟨records,ht⟩ := d24
    exact ⟨_, .compact 7379#usize 896#usize 23#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row23 ops) (by decide) (by rfl)
      (by change 8280≤logical.length;omega) h23 (by
        have ha : after 7379#usize 896#usize=8280#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 7379#usize 5#usize 7384#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 7384#usize 896#usize 8280#usize rfl]
        have hr : U8.wrapping_add 23#u8 1#u8=24#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d22 : ∃ records, Domain ops logical 27#u8 6478#usize 22#u8 records := by
    obtain ⟨records,ht⟩ := d23
    exact ⟨_, .compact 6478#usize 896#usize 22#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row22 ops) (by decide) (by rfl)
      (by change 7379≤logical.length;omega) h22 (by
        have ha : after 6478#usize 896#usize=7379#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 6478#usize 5#usize 6483#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 6483#usize 896#usize 7379#usize rfl]
        have hr : U8.wrapping_add 22#u8 1#u8=23#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d21 : ∃ records, Domain ops logical 27#u8 5577#usize 21#u8 records := by
    obtain ⟨records,ht⟩ := d22
    exact ⟨_, .compact 5577#usize 896#usize 21#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row21 ops) (by decide) (by rfl)
      (by change 6478≤logical.length;omega) h21 (by
        have ha : after 5577#usize 896#usize=6478#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 5577#usize 5#usize 5582#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 5582#usize 896#usize 6478#usize rfl]
        have hr : U8.wrapping_add 21#u8 1#u8=22#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d20 : ∃ records, Domain ops logical 27#u8 4676#usize 20#u8 records := by
    obtain ⟨records,ht⟩ := d21
    exact ⟨_, .compact 4676#usize 896#usize 20#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row20 ops) (by decide) (by rfl)
      (by change 5577≤logical.length;omega) h20 (by
        have ha : after 4676#usize 896#usize=5577#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 4676#usize 5#usize 4681#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 4681#usize 896#usize 5577#usize rfl]
        have hr : U8.wrapping_add 20#u8 1#u8=21#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d19 : ∃ records, Domain ops logical 27#u8 3775#usize 19#u8 records := by
    obtain ⟨records,ht⟩ := d20
    exact ⟨_, .compact 3775#usize 896#usize 19#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row19 ops) (by decide) (by rfl)
      (by change 4676≤logical.length;omega) h19 (by
        have ha : after 3775#usize 896#usize=4676#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 3775#usize 5#usize 3780#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 3780#usize 896#usize 4676#usize rfl]
        have hr : U8.wrapping_add 19#u8 1#u8=20#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d18 : ∃ records, Domain ops logical 27#u8 2874#usize 18#u8 records := by
    obtain ⟨records,ht⟩ := d19
    exact ⟨_, .compact 2874#usize 896#usize 18#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row18 ops) (by decide) (by rfl)
      (by change 3775≤logical.length;omega) h18 (by
        have ha : after 2874#usize 896#usize=3775#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 2874#usize 5#usize 2879#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 2879#usize 896#usize 3775#usize rfl]
        have hr : U8.wrapping_add 18#u8 1#u8=19#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d17 : ∃ records, Domain ops logical 27#u8 1973#usize 17#u8 records := by
    obtain ⟨records,ht⟩ := d18
    exact ⟨_, .compact 1973#usize 896#usize 17#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row17 ops) (by decide) (by rfl)
      (by change 2874≤logical.length;omega) h17 (by
        have ha : after 1973#usize 896#usize=2874#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 1973#usize 5#usize 1978#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 1978#usize 896#usize 2874#usize rfl]
        have hr : U8.wrapping_add 17#u8 1#u8=18#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d16 : ∃ records, Domain ops logical 27#u8 1072#usize 16#u8 records := by
    obtain ⟨records,ht⟩ := d17
    exact ⟨_, .compact 1072#usize 896#usize 16#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row16 ops) (by decide) (by rfl)
      (by change 1973≤logical.length;omega) h16 (by
        have ha : after 1072#usize 896#usize=1973#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 1072#usize 5#usize 1077#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 1077#usize 896#usize 1973#usize rfl]
        have hr : U8.wrapping_add 16#u8 1#u8=17#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d15 : ∃ records, Domain ops logical 27#u8 171#usize 15#u8 records := by
    obtain ⟨records,ht⟩ := d16
    exact ⟨_, .compact 171#usize 896#usize 15#u8 2#u8 28 records
      (by decide) (PV_RunJoin_RowShapes41.row15 ops) (by decide) (by rfl)
      (by change 1072≤logical.length;omega) h15 (by
        have ha : after 171#usize 896#usize=1072#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 171#usize 5#usize 176#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 176#usize 896#usize 1072#usize rfl]
        have hr : U8.wrapping_add 15#u8 1#u8=16#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d14 : ∃ records, Domain ops logical 27#u8 134#usize 14#u8 records := by
    obtain ⟨records,ht⟩ := d15
    exact ⟨_, .compact 134#usize 32#usize 14#u8 3#u8 1 records
      (by decide) (PV_RunJoin_RowShapes41.row14 ops) (by decide) (by rfl)
      (by change 171≤logical.length;omega) h14 (by
        have ha : after 134#usize 32#usize=171#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 134#usize 5#usize 139#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 139#usize 32#usize 171#usize rfl]
        have hr : U8.wrapping_add 14#u8 1#u8=15#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d13 : ∃ records, Domain ops logical 27#u8 129#usize 13#u8 records := by
    obtain ⟨records,ht⟩ := d14
    exact ⟨_, .copy 129#usize 0#usize 13#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row13 ops) (by decide)
      (by change 134≤logical.length;omega) (by
        have ha : after 129#usize 0#usize=134#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 129#usize 5#usize 134#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 134#usize 0#usize 134#usize rfl]
        have hr : U8.wrapping_add 13#u8 1#u8=14#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d12 : ∃ records, Domain ops logical 27#u8 124#usize 12#u8 records := by
    obtain ⟨records,ht⟩ := d13
    exact ⟨_, .copy 124#usize 0#usize 12#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row12 ops) (by decide)
      (by change 129≤logical.length;omega) (by
        have ha : after 124#usize 0#usize=129#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 124#usize 5#usize 129#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 129#usize 0#usize 129#usize rfl]
        have hr : U8.wrapping_add 12#u8 1#u8=13#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d11 : ∃ records, Domain ops logical 27#u8 119#usize 11#u8 records := by
    obtain ⟨records,ht⟩ := d12
    exact ⟨_, .copy 119#usize 0#usize 11#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row11 ops) (by decide)
      (by change 124≤logical.length;omega) (by
        have ha : after 119#usize 0#usize=124#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 119#usize 5#usize 124#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 124#usize 0#usize 124#usize rfl]
        have hr : U8.wrapping_add 11#u8 1#u8=12#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d10 : ∃ records, Domain ops logical 27#u8 114#usize 10#u8 records := by
    obtain ⟨records,ht⟩ := d11
    exact ⟨_, .copy 114#usize 0#usize 10#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row10 ops) (by decide)
      (by change 119≤logical.length;omega) (by
        have ha : after 114#usize 0#usize=119#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 114#usize 5#usize 119#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 119#usize 0#usize 119#usize rfl]
        have hr : U8.wrapping_add 10#u8 1#u8=11#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d9 : ∃ records, Domain ops logical 27#u8 109#usize 9#u8 records := by
    obtain ⟨records,ht⟩ := d10
    exact ⟨_, .copy 109#usize 0#usize 9#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row9 ops) (by decide)
      (by change 114≤logical.length;omega) (by
        have ha : after 109#usize 0#usize=114#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 109#usize 5#usize 114#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 114#usize 0#usize 114#usize rfl]
        have hr : U8.wrapping_add 9#u8 1#u8=10#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d8 : ∃ records, Domain ops logical 27#u8 104#usize 8#u8 records := by
    obtain ⟨records,ht⟩ := d9
    exact ⟨_, .copy 104#usize 0#usize 8#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row8 ops) (by decide)
      (by change 109≤logical.length;omega) (by
        have ha : after 104#usize 0#usize=109#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 104#usize 5#usize 109#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 109#usize 0#usize 109#usize rfl]
        have hr : U8.wrapping_add 8#u8 1#u8=9#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d7 : ∃ records, Domain ops logical 27#u8 99#usize 7#u8 records := by
    obtain ⟨records,ht⟩ := d8
    exact ⟨_, .copy 99#usize 0#usize 7#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row7 ops) (by decide)
      (by change 104≤logical.length;omega) (by
        have ha : after 99#usize 0#usize=104#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 99#usize 5#usize 104#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 104#usize 0#usize 104#usize rfl]
        have hr : U8.wrapping_add 7#u8 1#u8=8#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d6 : ∃ records, Domain ops logical 27#u8 94#usize 6#u8 records := by
    obtain ⟨records,ht⟩ := d7
    exact ⟨_, .copy 94#usize 0#usize 6#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row6 ops) (by decide)
      (by change 99≤logical.length;omega) (by
        have ha : after 94#usize 0#usize=99#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 94#usize 5#usize 99#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 99#usize 0#usize 99#usize rfl]
        have hr : U8.wrapping_add 6#u8 1#u8=7#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d5 : ∃ records, Domain ops logical 27#u8 89#usize 5#u8 records := by
    obtain ⟨records,ht⟩ := d6
    exact ⟨_, .copy 89#usize 0#usize 5#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row5 ops) (by decide)
      (by change 94≤logical.length;omega) (by
        have ha : after 89#usize 0#usize=94#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 89#usize 5#usize 94#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 94#usize 0#usize 94#usize rfl]
        have hr : U8.wrapping_add 5#u8 1#u8=6#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d4 : ∃ records, Domain ops logical 27#u8 84#usize 4#u8 records := by
    obtain ⟨records,ht⟩ := d5
    exact ⟨_, .copy 84#usize 0#usize 4#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row4 ops) (by decide)
      (by change 89≤logical.length;omega) (by
        have ha : after 84#usize 0#usize=89#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 84#usize 5#usize 89#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 89#usize 0#usize 89#usize rfl]
        have hr : U8.wrapping_add 4#u8 1#u8=5#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d3 : ∃ records, Domain ops logical 27#u8 79#usize 3#u8 records := by
    obtain ⟨records,ht⟩ := d4
    exact ⟨_, .copy 79#usize 0#usize 3#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row3 ops) (by decide)
      (by change 84≤logical.length;omega) (by
        have ha : after 79#usize 0#usize=84#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 79#usize 5#usize 84#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 84#usize 0#usize 84#usize rfl]
        have hr : U8.wrapping_add 3#u8 1#u8=4#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d2 : ∃ records, Domain ops logical 27#u8 42#usize 2#u8 records := by
    obtain ⟨records,ht⟩ := d3
    exact ⟨_, .copy 42#usize 32#usize 2#u8 1#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row2 ops) (by decide)
      (by change 79≤logical.length;omega) (by
        have ha : after 42#usize 32#usize=79#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 42#usize 5#usize 47#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 47#usize 32#usize 79#usize rfl]
        have hr : U8.wrapping_add 2#u8 1#u8=3#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d1 : ∃ records, Domain ops logical 27#u8 37#usize 1#u8 records := by
    obtain ⟨records,ht⟩ := d2
    exact ⟨_, .copy 37#usize 0#usize 1#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row1 ops) (by decide)
      (by change 42≤logical.length;omega) (by
        have ha : after 37#usize 0#usize=42#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 37#usize 5#usize 42#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 42#usize 0#usize 42#usize rfl]
        have hr : U8.wrapping_add 1#u8 1#u8=2#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  have d0 : ∃ records, Domain ops logical 27#u8 32#usize 0#u8 records := by
    obtain ⟨records,ht⟩ := d1
    exact ⟨_, .copy 32#usize 0#usize 0#u8 0#u8 records
      (by decide) (PV_RunJoin_RowShapes41.row0 ops) (by decide)
      (by change 37≤logical.length;omega) (by
        have ha : after 32#usize 0#usize=37#usize := by
          unfold after
          rw [PV_RunJoin_LayoutArithmetic41.add 32#usize 5#usize 37#usize rfl,
            PV_RunJoin_LayoutArithmetic41.add 37#usize 0#usize 37#usize rfl]
        have hr : U8.wrapping_add 0#u8 1#u8=1#u8 := by
          apply UScalar.eq_of_val_eq
          rw [U8.wrapping_add_val_eq]
          rfl
        simpa only [ha,hr] using ht)⟩
  exact d0
#print axioms domain
end R1Z.PV_RunJoin_LayoutDomain41
