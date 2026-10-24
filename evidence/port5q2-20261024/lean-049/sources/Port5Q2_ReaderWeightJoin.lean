import Port5Q2_ReaderWeights
import Port5Q2_ReaderFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderWeightJoin
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Sections (readList)
abbrev K := aspis_core.field.QM31

theorem sequence (bytes : Slice U8) (n : Nat) (start last : Usize) (xs : List K)
    (actual : Port5Q2_ReaderWeights.reads CheckpointBytes3Reader.readK bytes n start=ok (.Ok (xs,last))) :
    readList CheckpointBytes3Reader.readK n ⟨bytes,start⟩=ok (.Ok (xs,⟨bytes,last⟩)) := by
  induction n generalizing start last xs with
  | zero =>
    have same := core.result.Result.Ok.inj (Result.ok.inj actual)
    have hx := congrArg Prod.fst same
    have hl := congrArg Prod.snd same
    dsimp only at hx hl
    subst xs last
    rfl
  | succ n ih =>
    unfold Port5Q2_ReaderWeights.reads at actual
    obtain ⟨⟨value,out⟩,called,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
    cases value with
    | Err e => cases h
    | Ok x =>
      obtain ⟨rest,tail,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ h
      cases rest with
      | Err e => cases h
      | Ok pair =>
        rcases pair with ⟨ys,finish⟩
        have same := core.result.Result.Ok.inj (Result.ok.inj h)
        have hx := congrArg Prod.fst same
        have hl := congrArg Prod.snd same
        dsimp only at hx hl
        subst xs last
        have frame := Port5Q2_ReaderFrame.readK ⟨bytes,start⟩ out (.Ok x) called
        have outEq : out=⟨bytes,out.at⟩ := by
          cases out
          simp only [verifier.Reader.mk.injEq]
          exact ⟨frame,True.intro⟩
        have rest := ih out.at finish ys tail
        unfold readList
        rw [called]
        simp only [bind_tc_ok,Aeneas.Std.uncurry]
        rw [outEq,rest]
        rfl

/-- Accepted CURRENT native helper on its SAME Vec/input/cursor refines the
retained weight helper. The source read sequence is derived, not assumed. -/
theorem accepted (bytes : Slice U8) (start finish : Usize)
    (v out : alloc.vec.Vec K)
    (actual : Port5Q2_ReaderWeights.weights CheckpointBytes3Reader.readK bytes start v=ok (.Ok (out,finish))) :
    CheckpointBytes4Ops.readWeights bytes start v=ok (.Ok (out,finish)) := by
  rw [Port5Q2_ReaderWeights.exact] at actual
  obtain ⟨result,called,h⟩ := OraclePortCkptAbiTry.bind_success _ _ _ actual
  cases result with
  | Err e => cases h
  | Ok pair =>
    rcases pair with ⟨xs,last⟩
    have same := core.result.Result.Ok.inj (Result.ok.inj h)
    have weightsEq := congrArg (fun pair : alloc.vec.Vec K × Usize => pair.1.val) same
    have lastEq := congrArg Prod.snd same
    dsimp only at weightsEq lastEq
    subst finish
    have seq := sequence bytes v.val.length start last xs called
    have count := CheckpointBytes4Sections.read_list_length CheckpointBytes3Reader.readK
      v.val.length ⟨bytes,start⟩ ⟨bytes,last⟩ xs seq
    have content := Port5Q2_ReaderWeights.write_shape [] v.val xs v.property count
    have outContent : out.val=xs := weightsEq.symm.trans content
    obtain ⟨iter,loopRun,contents,cursor⟩ := CheckpointBytes4Weights.loop_success
      CheckpointBytes3Reader.readK v.val [] [] xs ⟨bytes,start⟩ ⟨bytes,last⟩
      (by simpa using v.property) seq
    change (do
      let result ← CheckpointBytes4Sections.weightLoop CheckpointBytes3Reader.readK
        v.val.length ⟨bytes,start⟩ ⟨⟨v.val,v.property⟩,0⟩
      match result with
      | .Err e => ok (.Err e)
      | .Ok (it,r) => ok (.Ok (⟨it.slice.val,it.slice.property⟩,r.at))
      : Result (core.result.Result (alloc.vec.Vec K × Usize) verifier.Error)) = _
    simp only [List.nil_append,List.append_nil,List.length_nil] at loopRun contents
    rw [loopRun]
    simp only [bind_tc_ok,Aeneas.Std.uncurry]
    apply congrArg Result.ok
    apply congrArg core.result.Result.Ok
    apply Prod.ext
    · exact Subtype.ext (contents.trans outContent.symm)
    · rfl

#print axioms sequence
#print axioms accepted
end AspisR1.Port5Q2_ReaderWeightJoin
end
