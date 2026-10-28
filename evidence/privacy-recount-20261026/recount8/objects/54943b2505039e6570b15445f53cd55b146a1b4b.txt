import R1Z.ProverCommitCircle25
import R1Z.ProverCommitFields20
/-! Nominal execution transport between the independently extracted semantic
and circle callers, retaining Aeneas failure/divergence and wire errors. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSemanticTransport26
open Aeneas Aeneas.Std Result

def mapR {α β : Type} (f : α → β) (m : Result α) : Result β := do
  let value ← m
  ok (f value)

theorem map_bind {α β γ : Type} (f : β → γ) (m : Result α) (k : α → Result β) :
    mapR f (do let a ← m; k a) = (do let a ← m; mapR f (k a)) := by
  cases m <;> rfl

theorem map_if {α β : Type} (f : α → β) (p : Prop) [Decidable p]
    (a b : Result α) : mapR f (if p then a else b) = if p then mapR f a else mapR f b := by
  by_cases h : p <;> simp [h]

theorem map_ok {α β : Type} (f : α → β) (value : α) : mapR f (ok value) = ok (f value) := rfl

abbrev SW := AspisR1SimSemantic20.aspis_core.field.wide_exact.WideExact
abbrev CW := AspisR1CircleCaller25.aspis_core.field.wide_exact.WideExact

def fromWide (v : SW) : CW :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
   ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩

theorem limbs (words : Array U32 8#usize) :
    mapR (Option.map fromWide) (AspisR1SimSemantic20.aspis_core.field.wide_exact.WideExact.from_limbs words) =
      AspisR1CircleCaller25.aspis_core.field.wide_exact.WideExact.from_limbs words := by
  simp only [AspisR1SimSemantic20.aspis_core.field.wide_exact.WideExact.from_limbs,
    AspisR1CircleCaller25.aspis_core.field.wide_exact.WideExact.from_limbs,
    AspisR1SimSemantic20.aspis_core.field.P,AspisR1CircleCaller25.aspis_core.field.P,map_bind,map_if,map_ok]
  rfl

theorem bytes (data : Slice U8) :
    mapR (Option.map fromWide) (AspisR1SimSemantic20.aspis_core.field.wide_exact.WideExact.from_le_bytes data) =
      AspisR1CircleCaller25.aspis_core.field.wide_exact.WideExact.from_le_bytes data := by
  simp only [AspisR1SimSemantic20.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    AspisR1CircleCaller25.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    AspisR1SimSemantic20.aspis_core.field.wide_exact.WideExact.BYTE_LEN,
    AspisR1CircleCaller25.aspis_core.field.wide_exact.WideExact.BYTE_LEN,map_bind,map_if,map_ok,limbs]
  rfl

theorem zero_test (x : SW) :
    core.cmp.PartialEq.ne.trait_default AspisR1CircleCaller25.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      (fromWide x).c1 AspisR1CircleCaller25.aspis_core.field.QM31.ZERO =
    core.cmp.PartialEq.ne.trait_default AspisR1SimSemantic20.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      x.c1 AspisR1SimSemantic20.aspis_core.field.QM31.ZERO := by
  simp only [core.cmp.PartialEq.ne.trait_default,
    AspisR1CircleCaller25.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,
    AspisR1CircleCaller25.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    AspisR1CircleCaller25.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    AspisR1CircleCaller25.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    AspisR1CircleCaller25.aspis_core.field.QM31.ZERO,
    AspisR1SimSemantic20.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,
    AspisR1SimSemantic20.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    AspisR1SimSemantic20.aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    AspisR1SimSemantic20.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    AspisR1SimSemantic20.aspis_core.field.QM31.ZERO,
    fromWide]
  rfl

def errorMap (r : core.result.Result Unit AspisR1SimSemantic20.r1_wire.Error) :
    core.result.Result Unit AspisR1CircleCaller25.r1_wire.Error :=
  match r with
  | .Ok value => .Ok value
  | .Err error => .Err (ProverCommitCircle25.fromError error)

theorem fields_bounded (remaining : Nat) (row : U8) (payload : alloc.vec.Vec U8) (value : Usize)
    (bound : payload.val.length < 32*(remaining+1)) :
    mapR errorMap (AspisR1SimSemantic20.r1_wire.fields20.validate row payload value) =
      AspisR1CircleCaller25.r1_wire.fields20.validate row payload value := by
  induction remaining generalizing payload value with
  | zero =>
    have short : alloc.vec.Vec.len payload < 32#usize := by change payload.val.length<32;omega
    rw [AspisR1SimSemantic20.r1_wire.fields20.validate,AspisR1CircleCaller25.r1_wire.fields20.validate]
    simp only [short,if_true,map_ok,errorMap]
  | succ n ih =>
    rw [AspisR1SimSemantic20.r1_wire.fields20.validate,AspisR1CircleCaller25.r1_wire.fields20.validate]
    by_cases short : alloc.vec.Vec.len payload < 32#usize
    · simp only [short,if_true,map_ok,errorMap]
    · simp only [short,if_false]
      have long : 32 ≤ payload.val.length := by change ¬payload.val.length<32 at short;omega
      have tailEq := ProverCommitFields20.drop_total payload long
      have tailBound : (Slice.drop payload 32#usize).val.length < 32*(n+1) := by
        simp only [Slice.getElem!_val_drop,List.length_drop]
        change payload.val.length-32<32*(n+1)
        omega
      have tailRec := ih (Slice.drop payload 32#usize) (Usize.wrapping_add value 1#usize) tailBound
      cases hp : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
          payload {«end»:=32#usize} with
      | fail e => simp only [mapR,hp,bind_tc_fail]
      | div => simp only [mapR,hp,bind_tc_div]
      | ok chunk =>
        simp only [hp,bind_tc_ok]
        rw [←bytes chunk]
        cases hd : AspisR1SimSemantic20.aspis_core.field.wide_exact.WideExact.from_le_bytes chunk with
        | fail e => simp only [mapR,hd,bind_tc_fail]
        | div => simp only [mapR,hd,bind_tc_div]
        | ok parsed =>
          cases parsed with
          | none => simp only [mapR,hd,bind_tc_ok,Option.map_none,errorMap,ProverCommitCircle25.fromError]
          | some x =>
            simp only [mapR,hd,bind_tc_ok,Option.map_some,
              AspisR1SimSemantic20.aspis_core.field.wide_exact.WideExact.impl.c1,
              AspisR1CircleCaller25.aspis_core.field.wide_exact.WideExact.impl.c1,zero_test]
            cases he : core.cmp.PartialEq.ne.trait_default
                AspisR1SimSemantic20.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                x.c1 AspisR1SimSemantic20.aspis_core.field.QM31.ZERO with
            | fail e => simp only [he,bind_tc_fail]
            | div => simp only [he,bind_tc_div]
            | ok bad =>
              simp only [he,bind_tc_ok]
              cases bad with
              | true => simp only [if_true,bind_tc_ok,errorMap,ProverCommitCircle25.fromError]
              | false =>
                simp only [Bool.false_eq_true,if_false,tailEq,bind_tc_ok,
                  ProverCommitFields20.clone_bytes,lift]
                exact tailRec

theorem fields (row : U8) (payload : alloc.vec.Vec U8) (value : Usize) :
    mapR errorMap (AspisR1SimSemantic20.r1_wire.fields20.validate row payload value) =
      AspisR1CircleCaller25.r1_wire.fields20.validate row payload value :=
  fields_bounded payload.val.length row payload value (by omega)

theorem shape (row : U8) : AspisR1SimSemantic20.r1_wire.row_shape row = AspisR1CircleCaller25.r1_wire.row_shape row := by
  simp only [AspisR1SimSemantic20.r1_wire.row_shape,AspisR1CircleCaller25.r1_wire.row_shape,
    AspisR1SimSemantic20.r1_wire.CLAIMS,AspisR1CircleCaller25.r1_wire.CLAIMS,
    AspisR1SimSemantic20.r1_wire.POINTS,AspisR1CircleCaller25.r1_wire.POINTS,
    AspisR1SimSemantic20.r1_wire.LANES,AspisR1CircleCaller25.r1_wire.LANES]
  rfl

theorem unit_finish {E : Type} (r : core.result.Result Unit E) :
    (match r with | .Ok _ => ok (core.result.Result.Ok ()) | .Err _ => ok r) = ok r := by
  cases r with
  | Ok value => cases value; rfl
  | Err error => rfl

theorem checked (row : U8) (record : Slice U8) :
    mapR errorMap (AspisR1SimSemantic20.r1_wire.semantic20.checked row record) =
      AspisR1CircleCaller25.r1_wire.semantic20.checked row record := by
  simp only [AspisR1SimSemantic20.r1_wire.semantic20.checked,AspisR1CircleCaller25.r1_wire.semantic20.checked,
    map_bind,shape]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro o ho
  cases o with
  | none => rfl
  | some pair =>
    rcases pair with ⟨tag,size⟩
    dsimp only [Aeneas.Std.uncurry]
    simp only [map_bind,map_if,map_ok]
    repeat
      first
      | rfl
      | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro v hv)
      | (split <;> try simp_all only [map_bind,map_if,map_ok,if_true,if_false,errorMap,ProverCommitCircle25.fromError])
    all_goals
      try simp only [unit_finish]
      rw [←fields]
      simp only [mapR,Aeneas.Std.bind_assoc_eq,bind_tc_ok,unit_finish]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value hv
      cases value <;> rfl

#print axioms shape
#print axioms unit_finish
#print axioms checked

#print axioms fields_bounded
#print axioms fields

#print axioms zero_test

#print axioms map_bind
#print axioms map_if
#print axioms map_ok
#print axioms limbs
#print axioms bytes
end R1Z.ProverCommitSemanticTransport26
