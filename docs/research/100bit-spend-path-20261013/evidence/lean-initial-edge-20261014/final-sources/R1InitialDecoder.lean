import R1InitialTrace
import R1PublicInitParse
import R1BackgroundOutputMap

/-! First-round completing decoder. The fixed public prefix is checked;
the C1 root comes from the queried address, not an oracle-dependent input. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InitialDecoder
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

abbrev Output (Cv : Type) := State × Chal Cv
abbrev Completion (Cv : Type) (L : Nat) :=
  BS (Addr L) State State × List (Addr L × Option State) ×
    (State → List State → Output Cv)

def output (p : Params M Cv L) (c1 : State) (x : State) (bs : List State) : Output Cv :=
  (c1, (p.σ 0 (bs.headD default), x))

def decode (p : Params M Cv L) (hD : 5 ≤ p.D) (pubBytes : Bytes)
    (init : Addr L) (_T : Table (Addr L) State) : Option (Completion Cv L) :=
  match PublicInitParse.parse pubBytes init with
  | none => none
  | some c1 => some (InitialSamplerLaw.own p init (PublicInitFrame.row0 p hD),
      [], output p c1)

theorem decode_initial (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pubBytes : Bytes) (hlen : pubBytes.length < 2^32)
    (hL : 75 + pubBytes.length ≤ L) (c1 : State) (T : Table (Addr L) State) :
    decode p hD pubBytes (PublicInitFrame.addr pubBytes hL c1) T =
      some (InitialSamplerLaw.own p (PublicInitFrame.addr pubBytes hL c1)
        (PublicInitFrame.row0 p hD), [], output p c1) := by
  simp only [decode, PublicInitParse.parse_addr pubBytes hlen hL c1]

theorem decodes_initializer (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pubBytes : Bytes) (hlen : pubBytes.length < 2^32)
    (hL : 75 + pubBytes.length ≤ L) (c1 : State)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hi : Read tr (PublicInitFrame.addr pubBytes hL c1))
    (ha : Read tr (PublicInitFrame.row0 p hD (H (PublicInitFrame.addr pubBytes hL c1))))
    (hsq : Read tr (squeezeA p (H (PublicInitFrame.row0 p hD
      (H (PublicInitFrame.addr pubBytes hL c1))))))
    (had : Read tr (advanceA p (H (PublicInitFrame.row0 p hD
      (H (PublicInitFrame.addr pubBytes hL c1)))))) :
    let init := PublicInitFrame.addr pubBytes hL c1
    let a := PublicInitFrame.row0 p hD (H init)
    let T := tableBefore emptyTable tr init
    ∃ own pend g, decode p hD pubBytes init T = some (own, pend, g) ∧
      bfollow g (traceFrom tr init) own pend T =
        some (c1, (p.σ 0 (H (squeezeA p (H a))), H (advanceA p (H a)))) := by
  dsimp only
  let init := PublicInitFrame.addr pubBytes hL c1
  let T := tableBefore emptyTable tr init
  let own := InitialSamplerLaw.own p init (PublicInitFrame.row0 p hD)
  refine ⟨own, [], output p c1, decode_initial p hD pubBytes hlen hL c1 T, ?_⟩
  have hf := InitialTrace.follows p hD H tr Qtot hcons hQ hold init hi ha hsq had 0
  have hm := BackgroundOutputMap.bfollow_map (fun ch : Chal Cv => (c1, ch))
    (fun x bs => (p.σ 0 (bs.headD default), x)) (traceFrom tr init) own [] T
  rw [hf] at hm
  exact hm

theorem output_law (p : Params M Cv L) (hD : 5 ≤ p.D) (init : Addr L)
    (c1 : State) (obs : Output Cv → ℚ) :
    blaw (output p c1) obs (InitialSamplerLaw.own p init (PublicInitFrame.row0 p hD)) [] =
      mean (fun b => mean (fun x => obs (c1, (p.σ 0 b, x)))) :=
  InitialSamplerLaw.own_law p init (PublicInitFrame.row0 p hD) 0
    (fun ch => (c1, ch)) obs

#print axioms decode_initial
#print axioms decodes_initializer
#print axioms output_law
end AspisR1.InitialDecoder
end
