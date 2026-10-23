import S9CurrentCheckpointKDecoderCMMapV1
import AspisR1DecodeKFullParserCanonicalityCMQ

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentCheckpointKDecoderQMMapV1
open AspisR1S9CurrentCheckpointKDecoderCMMapV1
abbrev CurQM := AspisR1S9CurrentCheckpointKDecoderV1.field.QM31
abbrev OldQM := AspisR1DecodeKFullV10.aspis_core.field.QM31

def toOldQM (q : CurQM) : OldQM := ⟨toOldCM q.c0,toOldCM q.c1⟩

def currentOptionBind {A B : Type} (m : Result (Option A)) (next : A → Result (Option B)) :
    Result (Option B) := do
  let value ← m
  let cf ← AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitTry.branch value
  match cf with
  | .Continue x => next x
  | .Break residual => AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual B residual

def oldOptionBind {A B : Type} (m : Result (Option A)) (next : A → Result (Option B)) :
    Result (Option B) := do
  let value ← m
  let cf ← AspisR1DecodeKFullV10.core.option.Option.Insts.CoreOpsTry_traitTry.branch value
  match cf with
  | .Continue x => next x
  | .Break residual => AspisR1DecodeKFullV10.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual B residual

private theorem common_bind_map {A B C : Type} (f : B → C) (m : Result A)
    (sourceNext : A → Result B) (targetNext : A → Result C)
    (hnext : ∀ x, mapResult f (sourceNext x) = targetNext x) :
    mapResult f (m >>= sourceNext) = (m >>= targetNext) := by
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq id f m m sourceNext targetNext
  · cases m <;> rfl
  · exact hnext

private theorem option_bind_map {A A' B B' : Type} (g : A → A') (f : B → B')
    (source : Result (Option A)) (target : Result (Option A'))
    (sourceNext : A → Result (Option B)) (targetNext : A' → Result (Option B'))
    (hfirst : mapResult (Option.map g) source = target)
    (hnext : ∀ x, mapResult (Option.map f) (sourceNext x) = targetNext (g x)) :
    mapResult (Option.map f) (currentOptionBind source sourceNext) = oldOptionBind target targetNext := by
  unfold currentOptionBind oldOptionBind
  apply AspisR1S9SourceResultTransportV1.mapResult_bind_eq (Option.map g) (Option.map f)
    source target _ _ hfirst
  intro value
  cases value with
  | none =>
    have hdisc : Aeneas.Std.read_discriminant
      (none : Option Aeneas.Std.core.convert.Infallible) = 0#isize := rfl
    simp [AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      AspisR1DecodeKFullV10.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      AspisR1DecodeKFullV10.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      Aeneas.Std.massert,hdisc,mapResult,AspisR1S9SourceResultTransportV1.mapResult]
  | some x =>
    simpa only [Option.map_some,
      AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      AspisR1DecodeKFullV10.core.option.Option.Insts.CoreOpsTry_traitTry.branch,bind_tc_ok] using hnext x

/-- Complete current-to-retained checkpoint QM decoder result map, with every
slice failure, None, error and divergence retained. No success/width premise. -/
theorem qm_decoder_map (bytes : Slice U8) :
    mapResult (Option.map toOldQM)
      (AspisR1S9CurrentCheckpointKDecoderV1.field.QM31.from_le_bytes bytes) =
      AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes := by
  unfold AspisR1S9CurrentCheckpointKDecoderV1.field.QM31.from_le_bytes
    AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes
  apply common_bind_map
  intro s0
  let currentNext (a : CurCM) : Result (Option CurQM) := do
    let s1 ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      {start := 8#usize, «end» := 16#usize}
    currentOptionBind (AspisR1S9CurrentCheckpointKDecoderV1.field.CM31.from_le_bytes s1)
      (fun b => .ok (some ({c0 := a,c1 := b} : CurQM)))
  let oldNext (a : OldCM) : Result (Option OldQM) := do
    let s1 ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      {start := 8#usize, «end» := 16#usize}
    oldOptionBind (AspisR1DecodeKFullV10.aspis_core.field.CM31.from_le_bytes s1)
      (fun b => .ok (some ({c0 := a,c1 := b} : OldQM)))
  have hmap : mapResult (Option.map toOldQM)
      (currentOptionBind (AspisR1S9CurrentCheckpointKDecoderV1.field.CM31.from_le_bytes s0) currentNext) =
      oldOptionBind (AspisR1DecodeKFullV10.aspis_core.field.CM31.from_le_bytes s0) oldNext := by
    refine option_bind_map toOldCM toOldQM
      (AspisR1S9CurrentCheckpointKDecoderV1.field.CM31.from_le_bytes s0)
      (AspisR1DecodeKFullV10.aspis_core.field.CM31.from_le_bytes s0)
      currentNext oldNext (cm_decoder_map s0) ?_
    intro a
    dsimp only [currentNext,oldNext]
    apply common_bind_map
    intro s1
    exact option_bind_map toOldCM toOldQM
      (AspisR1S9CurrentCheckpointKDecoderV1.field.CM31.from_le_bytes s1)
      (AspisR1DecodeKFullV10.aspis_core.field.CM31.from_le_bytes s1)
      (fun b => .ok (some ({c0 := a,c1 := b} : CurQM)))
      (fun b => .ok (some ({c0 := toOldCM a,c1 := b} : OldQM)))
      (cm_decoder_map s1) (fun b => rfl)
  simpa only [currentOptionBind,oldOptionBind,currentNext,oldNext,CurQM,OldQM,CurCM,OldCM] using hmap


def Canonical (q : CurQM) : Prop :=
  q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
  q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

/-- Reuses the retained FullV10 parser theorem on the same concrete current
source execution through the complete result map, without a decoder premise. -/
theorem current_decoder_success_canonical (bytes : Slice U8) (q : CurQM)
    (success : AspisR1S9CurrentCheckpointKDecoderV1.field.QM31.from_le_bytes bytes = .ok (some q)) :
    Canonical q := by
  have hm := qm_decoder_map bytes
  rw [success] at hm
  have hold : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes = .ok (some (toOldQM q)) := hm.symm
  have hc := AspisR1DecodeKFullParserCanonicality.qm31_from_le_bytes_success_canonical bytes (toOldQM q) hold
  have hp : AspisR1DecodeKFullV10.aspis_core.field.P.val = 2147483647 := by
    unfold AspisR1DecodeKFullV10.aspis_core.field.P
    rfl
  simpa only [Canonical,toOldQM,toOldCM,hp] using hc

#print axioms qm_decoder_map
#print axioms current_decoder_success_canonical
end AspisR1S9CurrentCheckpointKDecoderQMMapV1
