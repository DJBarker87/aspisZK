import T2Nat_ReaderOps
import OraclePortCkptAbi4Decode
import FJg_OriginalDigitCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_ReaderScalarCanon
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish

def CanonK (q : K) : Prop := FJc_WeightValues.Canon (FIn_WeightsInstall.toQ q)
def CanonE (q : E) : Prop := FIo_WideValues.Canon (FIo_Install.toE q)

theorem k (r out : verifier.Reader) (q : K)
    (run : CheckpointBytes3Reader.readK r=ok (.Ok q,out)) : CanonK q := by
  unfold CheckpointBytes3Reader.readK at run
  obtain ⟨⟨bytes,last⟩,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨oq,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases oq with
  | none => cases run
  | some raw =>
    cases Result.ok.inj run
    have hc := OraclePortCkptAbi4Decode.decoded_canonical _ raw hq
    rcases hc with ⟨a,b,c,d⟩
    exact ⟨⟨a,b⟩,⟨c,d⟩⟩

theorem e (r out : verifier.Reader) (q : E)
    (run : CheckpointBytes3Reader.readE r=ok (.Ok q,out)) : CanonE q := by
  unfold CheckpointBytes3Reader.readE at run
  obtain ⟨⟨bytes,last⟩,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨oq,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases oq with
  | none => cases run
  | some raw =>
    cases Result.ok.inj run
    have hc := OraclePortCkptAbi4Decode.decoded_wide_canonical _ raw hq
    rcases hc with ⟨⟨a,b,c,d⟩,⟨e,f,g,h⟩⟩
    exact ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
#print axioms k
#print axioms e
end AspisR1.FJg_ReaderScalarCanon
end
