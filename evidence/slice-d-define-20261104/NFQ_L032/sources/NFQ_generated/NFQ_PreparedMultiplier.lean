import NFQ_COMBINED_IMPORT
set_option autoImplicit false
namespace NFQ_PreparedMultiplier
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedMaskTowerAdd
abbrev C := AspisR1SelectedMaskProbe.field.CM31
abbrev Q := AspisR1SelectedMaskProbe.field.QM31
abbrev Row := Array U32 3#usize
abbrev Prepared := AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier

def rowWords (r : Row) : List Nat := r.val.map (fun x => x.val)
def words (r : Prepared) : List (List Nat) := r.components.val.map rowWords

def spec (x : Q) : List (List Nat) :=
  let a := x.c0.a.val;let b := x.c0.b.val;let c := x.c1.a.val;let d := x.c1.b.val
  let ac := (a+c)%2147483647;let bd := (b+d)%2147483647
  [[a,b,(a+b)%2147483647],[c,d,(c+d)%2147483647],
   [ac,bd,(ac+bd)%2147483647]]

/-- Rust's guarded scalar sum equals the canonical natural spec. -/
theorem add_word (a b : Nat) (ha : a<2147483647) (hb : b<2147483647) :
    (if a+b≥2147483647 then a+b-2147483647 else a+b) = (a+b)%2147483647 := by
  by_cases h : 2147483647≤a+b
  · rw [if_pos h,Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h,Nat.mod_eq_of_lt (by omega)]

theorem row_source (c : C) (hc : CanonicalCM c) :
    ∃ r : Row,
      AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call () c=ok r ∧
      rowWords r=[c.a.val,c.b.val,(c.a.val+c.b.val)%2147483647] := by
  obtain ⟨s,run,value,canonical⟩ :=
    AspisR1.ExtractedMaskM31AddSub.current_add_mod c.a c.b hc.1 hc.2
  refine ⟨Array.make 3#usize [c.a,c.b,s],?_,?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,run,bind_tc_ok]
  · simp only [rowWords,List.map_cons,List.map_nil]
    exact congrArg (fun z => [c.a.val,c.b.val,z]) value

/-- Complete nine-word record, with no inner field-operation hypotheses. -/
theorem source (x : Q) (canonical : CanonicalQM x) :
    ∃ out : Prepared, AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new x=ok out ∧
      words out=spec x := by
  obtain ⟨c,run,c_canonical,ca,cb⟩ := current_cm_add_mod x.c0 x.c1 canonical.1 canonical.2
  obtain ⟨r0,run0,words0⟩:=row_source x.c0 canonical.1
  obtain ⟨r1,run1,words1⟩:=row_source x.c1 canonical.2
  obtain ⟨r2,run2,words2⟩:=row_source c c_canonical
  refine ⟨⟨Array.make 3#usize [r0,r1,r2]⟩,?_,?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new,
      run0,run1,run,run2,bind_tc_ok]
  · simp only [words,List.map_cons,List.map_nil,words0,words1,words2,ca,cb,spec]

#print axioms add_word
#print axioms row_source
#print axioms source
end NFQ_PreparedMultiplier
