import R1ProgramLabelRestriction
import R1CanonicalByteAddress
import R1UnifiedSampler

/-! Every address asked by the finite R1 sampler program is produced by a
bounded `Addr.ofBytes` constructor. This proves the all-continuations label
premise for the sampler itself; it does not cover arbitrary adversary queries. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedCanonicalLabels

open FS FS2 FS2.Duplex R0C.V3
open AspisR1.TranscriptView
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv C : Type} {L : Nat}

private theorem squeeze_canonical (p : Params M Cv L) (s : State) :
    CanonicalByteAddress.Canonical (squeezeA p s) :=
  CanonicalByteAddress.canonical_ofBytes _ _

private theorem advance_canonical (p : Params M Cv L) (s : State) :
    CanonicalByteAddress.Canonical (advanceA p s) :=
  CanonicalByteAddress.canonical_ofBytes _ _

private theorem absorb_canonical (p : Params M Cv L) (s : State)
    (l : Byte) (data : Bytes) (h : data.length ≤ p.D) :
    CanonicalByteAddress.Canonical (absorbA p s l data h) :=
  CanonicalByteAddress.canonical_ofBytes _ _

private theorem unified_absorb_canonical (p : Params M Cv L) (i : Nat)
    (P : UnifiedSampler.Prefix M Cv L) (m : M) :
    CanonicalByteAddress.Canonical (UnifiedSampler.absorb p i P m) := by
  exact absorb_canonical p (UnifiedSampler.stateOf p P) (p.lbl i) (p.enc m) (p.encLen m)

private theorem plain_allLabels (p : Params M Cv L) (a : Addr L) (i : Nat)
    (G : Chal Cv → C) (ha : CanonicalByteAddress.Canonical a) :
    ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical
      (DuplexSamplers.plain p a i G).toProgram := by
  simp only [DuplexSamplers.plain, Sampler.toProgram, ProgramLabelRestriction.AllLabels]
  exact ⟨ha, fun s => ⟨squeeze_canonical p s,
    fun b => ⟨advance_canonical p s, fun x => trivial⟩⟩⟩

private theorem initial_allLabels (p : Params M Cv L) (init : Addr L)
    (begin : State → Addr L) (i : Nat) (G : Chal Cv → C)
    (hinit : CanonicalByteAddress.Canonical init)
    (hbegin : ∀ s, CanonicalByteAddress.Canonical (begin s)) :
    ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical
      (DuplexSamplers.initial p init begin i G).toProgram := by
  simp only [DuplexSamplers.initial, Sampler.toProgram, ProgramLabelRestriction.AllLabels]
  exact ⟨hinit, fun s => ⟨hbegin s, fun a => ⟨squeeze_canonical p a,
    fun b => ⟨advance_canonical p a, fun x => trivial⟩⟩⟩⟩

private theorem reseeded_allLabels (p : Params M Cv L) (a : Addr L)
    (reseed : State → Addr L) (i : Nat) (G : Chal Cv → C)
    (ha : CanonicalByteAddress.Canonical a)
    (hreseed : ∀ s, CanonicalByteAddress.Canonical (reseed s)) :
    ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical
      (DuplexSamplers.reseeded p a reseed i G).toProgram := by
  simp only [DuplexSamplers.reseeded, Sampler.toProgram, ProgramLabelRestriction.AllLabels]
  exact ⟨ha, fun s => ⟨squeeze_canonical p s,
    fun b => ⟨advance_canonical p s,
      fun x => ⟨hreseed x, fun y => trivial⟩⟩⟩⟩

private theorem query_chain_allLabels (p : Params M Cv L)
    (out : List State → List State → C) : ∀ n s bs xs,
    ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical
      (QuerySampler.chain p out n s bs xs).toProgram := by
  intro n
  induction n with
  | zero => intro s bs xs; simp [QuerySampler.chain, Sampler.toProgram,
      ProgramLabelRestriction.AllLabels]
  | succ n ih =>
      intro s bs xs
      simp only [QuerySampler.chain, Sampler.toProgram, ProgramLabelRestriction.AllLabels]
      exact ⟨squeeze_canonical p s, fun b =>
        ⟨advance_canonical p s, fun x => ih x (bs ++ [b]) (xs ++ [x])⟩⟩

private theorem query_sampler_allLabels (p : Params M Cv L) (a : Addr L)
    (G : AspisV8R19.Q22SamplerProgram.Result → C)
    (ha : CanonicalByteAddress.Canonical a) :
    ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical
      (QuerySamplerBridge.sampler p a G).toProgram := by
  simp only [QuerySamplerBridge.sampler, Sampler.toProgram, ProgramLabelRestriction.AllLabels]
  exact ⟨ha, fun s => query_chain_allLabels p
    (fun bs xs => G (Q22.scanOut 8 Q22.q0 bs xs s)) 8 s [] []⟩

private theorem invalid_allLabels (p : Params M Cv L) :
    ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical
      (UnifiedSampler.invalid p).toProgram := by
  simp only [UnifiedSampler.invalid, Sampler.toProgram, ProgramLabelRestriction.AllLabels]
  exact ⟨squeeze_canonical p p.iv, fun _ => trivial⟩

theorem samp_allLabels (p : Params M Cv L) (hD : 5 ≤ p.D)
    (i : Nat) (P : UnifiedSampler.Prefix M Cv L) (m : Message M) :
    ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical
      (UnifiedSampler.samp p hD i P m).toProgram := by
  cases i with
  | zero =>
      cases m with
      | initial c1 =>
          change ProgramLabelRestriction.AllLabels CanonicalByteAddress.Canonical
            (DuplexSamplers.initial p
              (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1)
              (PublicInitFrame.row0 p hD) 0 TranscriptView.liftChallenge).toProgram
          apply initial_allLabels
          · exact CanonicalByteAddress.canonical_ofBytes _ _
          · intro s
            exact absorb_canonical p s 160 PublicInitFrame.emptyRecord hD
      | payload _ => exact invalid_allLabels p
  | succ j =>
      cases m with
      | initial _ => exact invalid_allLabels p
      | payload msg =>
          by_cases h26 : j + 1 = 26
          · simp only [UnifiedSampler.samp, h26, if_pos]
            apply reseeded_allLabels
            · exact unified_absorb_canonical p 26 P msg
            · intro s
              exact CanonicalByteAddress.canonical_ofBytes _ _
          · by_cases h31 : j + 1 = 31
            · simp only [UnifiedSampler.samp, h26, h31, if_neg, if_pos]
              exact query_sampler_allLabels p _ _ (unified_absorb_canonical p 31 P msg)
            · simp only [UnifiedSampler.samp, h26, h31, if_neg]
              exact plain_allLabels p _ _ _ (unified_absorb_canonical p (j + 1) P msg)

#print axioms samp_allLabels

end AspisR1.UnifiedCanonicalLabels
end
