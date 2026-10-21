import S8OwnedP6StrictParser
import S8OwnedP6LoopContracts

/-! Totality and acceptance contract for the complete emitted compact scan. -/
set_option autoImplicit false
noncomputable section
namespace S8OwnedP6Scan
open Aeneas Aeneas.Std Result ControlFlow
open S8OwnedP6
abbrev Q := aspis_core.field.QM31
abbrev Status := core.result.Result Unit CodecError

theorem parser_total (s : Slice U8) (hlen : s.val.length=16) :
    ∃ out : Option Q, aspis_core.field.QM31.from_le_bytes s=.ok out := by
  let arr : Array U8 16#usize := ⟨s.val,by change s.val.length=16; exact hlen⟩
  have hs : Array.to_slice arr=s := by apply Subtype.ext; rfl
  rw [← hs]
  exact ⟨_,AspisR1.S8OwnedP6StrictParser.source_refines arr⟩

/-- The complete chunk selected by an ordinal. Its contents and parse result
are explicit, so the scan model cannot choose a different byte observation. -/
def Good (bytes : Slice U8) (i : Nat) : Prop :=
  ∃ s : Slice U8, s.val=(bytes.val.drop (16*i)).take 16 ∧
    ∃ q : Q, aspis_core.field.QM31.from_le_bytes s=.ok (some q)

private theorem add_total (a b : Usize) (h : a.val+b.val≤Usize.max) :
    ∃ c : Usize, (a+b : Result Usize)=.ok c ∧ c.val=a.val+b.val := by
  apply WP.spec_imp_exists
  apply UScalar.add_spec
  simpa only [UScalar.max_USize_eq] using h

private theorem mul_total (a b : Usize) (h : a.val*b.val≤Usize.max) :
    ∃ c : Usize, (a*b : Result Usize)=.ok c ∧ c.val=a.val*b.val := by
  apply WP.spec_imp_exists
  apply UScalar.mul_spec
  simpa only [UScalar.max_USize_eq] using h

/-- One complete emitted scan iteration, with a semantically pinned chunk;
all checked offsets and slice operations succeed. -/
theorem scan_step (bytes : Slice U8) (index : Usize)
    (hi : index.val<bytes.val.length/16) :
    ∃ next : Usize, ∃ s : Slice U8, ∃ parsed : Option Q,
      next.val=index.val+1 ∧
      s.val=(bytes.val.drop (16*index.val)).take 16 ∧
      aspis_core.field.QM31.from_le_bytes s=.ok parsed ∧
      (Good bytes index.val ↔ parsed.isSome=true) ∧
      check_values_owned_loop.body bytes index=
        .ok (match parsed with
          | none => .done (some (.Err .NonCanonical))
          | some _ => .cont next) := by
  have hlen : bytes.val.length≤Usize.max := bytes.property
  have hb := S8OwnedP6LoopContracts.scan_offset_bounds bytes.val.length index.val hi
  obtain ⟨count,hcount,hcv⟩ :=
    UScalar.div_spec (x:=Slice.len bytes) (y:=16#usize) (by decide)
  change count.val=bytes.val.length/16 at hcv
  obtain ⟨at1,hat,hav⟩ := mul_total index 16#usize (by change index.val*16≤Usize.max; omega)
  change at1.val=index.val*16 at hav
  obtain ⟨end1,hend,hev⟩ := add_total at1 16#usize (by change at1.val+16≤Usize.max; omega)
  change end1.val=at1.val+16 at hev
  obtain ⟨s,hs,hcontents,hslen⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec ⟨at1,end1⟩ bytes
      (by change at1.val≤end1.val; omega) (by change end1.val≤bytes.val.length; omega))
  have hslen' : s.val.length=16 := by
    change s.val.length=end1.val-at1.val at hslen
    omega
  obtain ⟨parsed,hparse⟩ := parser_total s hslen'
  obtain ⟨next,hnext,hnv⟩ := add_total index 1#usize (by change index.val+1≤Usize.max; omega)
  change next.val=index.val+1 at hnv
  have hcontents' : s.val=(bytes.val.drop (16*index.val)).take 16 := by
    change s.val=List.extract bytes.val at1.val end1.val at hcontents
    simpa [List.extract,hav,hev,Nat.mul_comm] using hcontents
  have hgood : Good bytes index.val ↔ parsed.isSome=true := by
    constructor
    · rintro ⟨other,hother,q,hq⟩
      have heq : other=s := by apply Subtype.ext; exact hother.trans hcontents'.symm
      subst other
      rw [hparse] at hq
      have hp : parsed=some q := Result.ok.inj hq
      simp only [hp,Option.isSome_some]
    · intro hp
      cases parsed with
      | none => simp at hp
      | some q => exact ⟨s,hcontents',q,hparse⟩
  refine ⟨next,s,parsed,hnv,hcontents',hparse,hgood,?_⟩
  have hcond : index<count := by change index.val<count.val; omega
  have hs' : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes ⟨at1,end1⟩=.ok s := by
    rw [Slice.index_SliceIndexRangeUsizeSliceInst]; exact hs
  cases parsed <;>
    simp [check_values_owned_loop.body,hcount,hcond,hat,hend,hs',hparse,hnext,
      S8OwnedP6.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Every complete scan terminates normally, rejecting exactly when at least
one complete stored QM31 is noncanonical. The final partial chunk is ignored. -/
theorem scan_total_model (bytes : Slice U8) :
    ∃ out : Status, check_values_owned bytes=.ok out ∧
      (out=.Ok () ↔ ∀ j, j < bytes.val.length/16 → Good bytes j) ∧
      (out=.Ok () ∨ out=.Err .NonCanonical) := by
  let allGood := ∀ j, j < bytes.val.length/16 → Good bytes j
  have hs : WP.spec (check_values_owned_loop bytes 0#usize)
      (fun out => (out=none ↔ allGood) ∧
        (out=none ∨ out=some (.Err .NonCanonical))) := by
    unfold check_values_owned_loop
    refine loop.spec_decr_nat (fun i : Usize => bytes.val.length/16-i.val)
      (fun i => i.val≤bytes.val.length/16 ∧ ∀ j, j < i.val → Good bytes j)
      (fun out => (out=none ↔ allGood) ∧ (out=none ∨ out=some (.Err .NonCanonical)))
      (fun i => check_values_owned_loop.body bytes i) 0#usize ?_ ?_
    · intro i hinv
      rcases hinv with ⟨hib,hprefix⟩
      by_cases hi : i.val<bytes.val.length/16
      · obtain ⟨next,s,parsed,hnv,_hc,_hp,hgood,hstep⟩ := scan_step bytes i hi
        cases parsed with
        | none =>
          rw [hstep,WP.spec_ok]
          refine ⟨?_,Or.inr rfl⟩
          constructor
          · intro h; cases h
          · intro ha
            have hg := hgood.mp (ha i.val hi)
            simp at hg
        | some q =>
          rw [hstep,WP.spec_ok]
          constructor
          · refine ⟨by omega,?_⟩
            intro j hj
            by_cases he : j=i.val
            · subst j; exact hgood.mpr rfl
            · exact hprefix j (by omega)
          · omega
      · obtain ⟨count,hcount,hcv⟩ :=
          UScalar.div_spec (x:=Slice.len bytes) (y:=16#usize) (by decide)
        change count.val=bytes.val.length/16 at hcv
        have hcond : ¬ i<count := by change ¬ i.val<count.val; omega
        simp only [check_values_owned_loop.body,hcount,if_neg hcond,bind_tc_ok,WP.spec_ok]
        refine ⟨?_,Or.inl rfl⟩
        constructor
        · intro _ j hj; exact hprefix j (by omega)
        · intro _; rfl
    · change (0:Nat)≤bytes.val.length/16 ∧ ∀ j, j < 0 → Good bytes j
      exact ⟨by omega,by intro j hj; omega⟩
  obtain ⟨out,hrun,hequiv,hcases⟩ := WP.spec_imp_exists hs
  cases hcases with
  | inl h =>
    subst out
    refine ⟨.Ok (),?_,?_,Or.inl rfl⟩
    · simp only [check_values_owned,hrun,bind_tc_ok]
    · exact ⟨fun _ => hequiv.mp rfl,fun _ => rfl⟩
  | inr h =>
    subst out
    refine ⟨.Err .NonCanonical,?_,?_,Or.inr rfl⟩
    · simp only [check_values_owned,hrun,bind_tc_ok]
    · constructor
      · intro h; cases h
      · intro h; have hn := hequiv.mpr h; cases hn

#print axioms parser_total
#print axioms add_total
#print axioms mul_total
#print axioms scan_step
#print axioms scan_total_model
end S8OwnedP6Scan
