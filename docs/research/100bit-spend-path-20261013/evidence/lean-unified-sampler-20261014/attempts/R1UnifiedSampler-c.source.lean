import R1DuplexSamplers
import R1QuerySamplerBridge
import R1RowZeroCodec
import R1OpeningReseedFrame
import R1TranscriptView

/-! One sampler schedule for the 33 R1 challenges. Public bytes exclude C1:
C1 is the first prover message. This is an abstract-codec byte model, not a
Rust refinement, complete FS decoder, or security theorem. Wrong message
constructors use an explicit totalization branch and must be rejected by a
future protocol decision/classifier. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSampler

open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open TranscriptView

variable {M Cv : Type} {L : Nat}

structure Public (L : Nat) where
  pubBytes : Bytes
  initFits : 75 + pubBytes.length ≤ L
  tag : Byte

abbrev Prefix (M Cv : Type) (L : Nat) :=
  FS.Prefix (Public L) (Message M) (Challenge Cv)

def roundCount : Nat := 33

def stateOf (p : Params M Cv L) (P : Prefix M Cv L) : State :=
  match P.rounds.getLast? with
  | none => p.iv
  | some (_, ch) => ch.2

def absorb (p : Params M Cv L) (i : Nat) (P : Prefix M Cv L) (m : M) : Addr L :=
  absorbA p (stateOf p P) (p.lbl i) (p.enc m) (p.encLen m)

def messageValid : Nat → Message M → Prop
  | 0, .initial _ => True
  | _ + 1, .payload _ => True
  | _, _ => False

/-- Defined only to totalize the sampler outside the valid message schedule. -/
def invalid (p : Params M Cv L) : Sampler (Addr L) State (Challenge Cv) :=
  .ask (squeezeA p p.iv) fun _ => .done (.queries (.error 0), p.iv)

def liftQuery (r : AspisV8R19.Q22SamplerProgram.Result) : Challenge Cv :=
  (.queries r.1, r.2)

def samp (p : Params M Cv L) (hD : 5 ≤ p.D) (i : Nat)
    (P : Prefix M Cv L) (m : Message M) : Sampler (Addr L) State (Challenge Cv) :=
  match i, m with
  | 0, .initial c1 =>
      DuplexSamplers.initial p
        (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1)
        (PublicInitFrame.row0 p hD) 0 liftChallenge
  | 0, .payload _ => invalid p
  | j + 1, .payload msg =>
      let a := absorb p (j + 1) P msg
      if j + 1 = 26 then
        DuplexSamplers.reseeded p a
          (OpeningReseedFrame.addr P.statement.tag (by have := P.statement.initFits; omega))
          (j + 1) liftChallenge
      else if j + 1 = 31 then
        QuerySamplerBridge.sampler p a liftQuery
      else DuplexSamplers.plain p a (j + 1) liftChallenge
  | _ + 1, .initial _ => invalid p

theorem stateOf_ext (p : Params M Cv L) (P : Prefix M Cv L)
    (m : Message M) (ch : Challenge Cv) :
    stateOf p (P.ext m ch) = ch.2 := by
  simp [stateOf, FS.Prefix.ext]

theorem row_zero (p : Params M Cv L) (hD : 5 ≤ p.D)
    (P : Prefix M Cv L) (c1 : State) :
    samp p hD 0 P (.initial c1) = DuplexSamplers.initial p
      (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1)
      (PublicInitFrame.row0 p hD) 0 liftChallenge := rfl

theorem row_reseed (p : Params M Cv L) (hD : 5 ≤ p.D)
    (P : Prefix M Cv L) (m : M) :
    samp p hD 26 P (.payload m) = DuplexSamplers.reseeded p (absorb p 26 P m)
      (OpeningReseedFrame.addr P.statement.tag (by have := P.statement.initFits; omega))
      26 liftChallenge := rfl

theorem row_query (p : Params M Cv L) (hD : 5 ≤ p.D)
    (P : Prefix M Cv L) (m : M) :
    samp p hD 31 P (.payload m) =
      QuerySamplerBridge.sampler p (absorb p 31 P m) liftQuery := rfl

theorem row_ordinary (p : Params M Cv L) (hD : 5 ≤ p.D)
    (i : Nat) (hi0 : i ≠ 0) (hi26 : i ≠ 26) (hi31 : i ≠ 31)
    (P : Prefix M Cv L) (m : M) :
    samp p hD i P (.payload m) =
      DuplexSamplers.plain p (absorb p i P m) i liftChallenge := by
  cases i with
  | zero => contradiction
  | succ i => simp only [samp, hi26, hi31, ↓reduceIte]

theorem row_rho (p : Params M Cv L) (hD : 5 ≤ p.D)
    (P : Prefix M Cv L) (m : M) :
    samp p hD 32 P (.payload m) =
      DuplexSamplers.plain p (absorb p 32 P m) 32 liftChallenge := rfl

theorem firstCell_some (p : Params M Cv L) (hD : 5 ≤ p.D)
    (i : Nat) (P : Prefix M Cv L) (m : Message M) :
    firstCell (samp p hD i P m) ≠ none := by
  cases i with
  | zero => cases m <;> simp [samp, invalid, DuplexSamplers.initial, firstCell]
  | succ i =>
      cases m with
      | initial c1 => simp [samp, invalid, firstCell]
      | payload msg =>
          by_cases h26 : i + 1 = 26 <;> by_cases h31 : i + 1 = 31 <;>
            simp [samp, h26, h31, DuplexSamplers.reseeded,
              QuerySamplerBridge.sampler, DuplexSamplers.plain, firstCell]

#print axioms stateOf_ext
#print axioms row_zero
#print axioms row_reseed
#print axioms row_query
#print axioms row_ordinary
#print axioms row_rho
#print axioms firstCell_some

end AspisR1.UnifiedSampler
end
