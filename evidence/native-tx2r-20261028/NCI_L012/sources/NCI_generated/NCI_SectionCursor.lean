import CheckpointBytes4ReaderFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCI_SectionCursor
open Aeneas Aeneas.Std Result AspisR1Stage2
open CheckpointBytes4Sections

theorem successful_section (n : Nat) (r last : verifier.Reader) (xs : List K)
    (bound : r.at.val+16*n ≤ r.bytes.val.length)
    (success : readList CheckpointBytes3Reader.readK n r = ok (.Ok (xs,last))) :
    last.at.val = r.at.val+16*n ∧ last.bytes = r.bytes ∧ xs.length=n := by
  induction n generalizing r xs with
  | zero =>
    simp only [readList] at success
    have eq := core.result.Result.Ok.inj (Result.ok.inj success)
    have ex := congrArg Prod.fst eq
    have er := congrArg Prod.snd eq
    dsimp only at ex er
    subst xs last
    simp
  | succ n ih =>
    simp only [readList] at success
    obtain ⟨⟨value,out⟩,readRun,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
    cases value with
    | Err e => cases tail
    | Ok x =>
      have bound1 : r.at.val+16 ≤ r.bytes.val.length := by omega
      obtain ⟨_,_,_,advanced,backing⟩ := CheckpointBytes4ReaderFields.k_success r out x bound1 readRun
      obtain ⟨rest,restRun,tail⟩ := OraclePortCkptAbiTry.bind_success _ _ _ tail
      cases rest with
      | Err e => cases tail
      | Ok pair =>
        rcases pair with ⟨ys,finish⟩
        have eq := core.result.Result.Ok.inj (Result.ok.inj tail)
        have ex := congrArg Prod.fst eq
        have er := congrArg Prod.snd eq
        dsimp only at ex er
        subst xs last
        have bound2 : out.at.val+16*n ≤ out.bytes.val.length := by rw [backing]; omega
        obtain ⟨cursor,bytes,size⟩ := ih out ys bound2 restRun
        refine ⟨by omega,bytes.trans backing,by simp [size]⟩

#print axioms successful_section
end AspisR1.NCI_SectionCursor
