import NDO_JFp_SHADigest
import NDO_JHj_Seeds
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHs_PDA
open Classical
open Aeneas Aeneas.Std Result
open _root_.AdapterRw
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- Exact ordered SDK hash preimage, without seed separators or lengths. -/
def preimage (seeds : Slice (Slice U8)) (program : solana_pubkey.Pubkey) : Bytes :=
  ((seeds.val.flatMap (fun s => s.val)) ++ program.val ++
    [80#u8,114#u8,111#u8,103#u8,114#u8,97#u8,109#u8,68#u8,101#u8,114#u8,105#u8,
     118#u8,101#u8,100#u8,65#u8,100#u8,100#u8,114#u8,101#u8,115#u8,115#u8]).map decodeByte

def ValidSeeds (seeds : Slice (Slice U8)) : Prop :=
  seeds.val.length ≤ 16 ∧ ∀ s ∈ seeds.val, s.val.length ≤ 32

def prime : Nat := 2^255 - 19
/-- Edwards25519 d = -121665/121666 in the field. -/
def edwardsD : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555
/-- Mask sign bit, little endian; field operations below reduce Y modulo p. -/
def yCoordinate (h : State) : Nat :=
  (List.range 32).foldl (fun n i => n +
    ((bytes h).getD i 0).val % (if i = 31 then 128 else 256) * 256^i) 0
/-- Mathematical decompression-existence specification. Runtime/dalek
correspondence is an unadopted trust proposal, not a theorem in this module. -/
def OnCurve (h : State) : Prop :=
  let y := yCoordinate h % prime
  ∃ x : Nat, x < prime ∧
    ((edwardsD * y*y + 1) * x*x) % prime = (y*y + prime - 1) % prime

def OffCurve (h : State) : Prop := ¬ OnCurve h

/-- Host fallback mathematical model. SHA is the existing mathematical digest;
only per-call digest equations may supply its concrete value. -/
def derive (seeds : Slice (Slice U8)) (program : solana_pubkey.Pubkey) :
    Result (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError) :=
  if ValidSeeds seeds then
    let h := JFp_SHADigest.digest (preimage seeds program)
    if OnCurve h then ok (.Err .InvalidSeeds) else ok (.Ok (encodeState h))
  else ok (.Err .MaxSeedLengthExceeded)

theorem seed_error (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey)
    (h : ¬ ValidSeeds s) : derive s p = ok (.Err .MaxSeedLengthExceeded) := by
  simp only [derive, if_neg h]
#print axioms seed_error

theorem count_error (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey)
    (h : 16 < s.val.length) : derive s p = ok (.Err .MaxSeedLengthExceeded) := by
  apply seed_error
  intro hv
  exact Nat.not_le_of_gt h hv.1
#print axioms count_error

theorem length_error (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey)
    (seed : Slice U8) (mem : seed ∈ s.val) (h : 32 < seed.val.length) :
    derive s p = ok (.Err .MaxSeedLengthExceeded) := by
  apply seed_error
  intro hv
  exact Nat.not_le_of_gt h (hv.2 seed mem)
#print axioms length_error

theorem curve_error (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey)
    (valid : ValidSeeds s) (curve : OnCurve (JFp_SHADigest.digest (preimage s p))) :
    derive s p = ok (.Err .InvalidSeeds) := by
  simp only [derive, if_pos valid, if_pos curve]
#print axioms curve_error

theorem certified (s : Slice (Slice U8)) (p key : solana_pubkey.Pubkey)
    (valid : ValidSeeds s)
    (digestEquation : JFp_SHADigest.digest (preimage s p) = decodeState key)
    (offCurve : OffCurve (decodeState key)) : derive s p = ok (.Ok key) := by
  change ¬ OnCurve (decodeState key) at offCurve
  simp only [derive, if_pos valid, digestEquation, if_neg offCurve, array_roundtrip]
#print axioms certified

/-- Solana wrapper return-code interpretation; 0 is intercepted as success
before PubkeyError::from, and unsupported nonzero codes panic. -/
def syscallReturn (code : Nat) (output : solana_pubkey.Pubkey) :
    Result (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError) :=
  match code with
  | 0 => ok (.Ok output)
  | 1 => ok (.Err .InvalidSeeds)
  | 2 => ok (.Err .IllegalOwner)
  | _ => fail .panic

theorem syscall_success (k : solana_pubkey.Pubkey) : syscallReturn 0 k = ok (.Ok k) := rfl
#print axioms syscall_success
theorem syscall_curve (k : solana_pubkey.Pubkey) : syscallReturn 1 k = ok (.Err .InvalidSeeds) := rfl
#print axioms syscall_curve
theorem syscall_owner (k : solana_pubkey.Pubkey) : syscallReturn 2 k = ok (.Err .IllegalOwner) := rfl
#print axioms syscall_owner

/-- Caller maps every SDK error to InvalidAccountData. -/
def callerMap (r : core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError) :
    core.result.Result solana_pubkey.Pubkey solana_program_error.ProgramError :=
  match r with
  | .Ok k => .Ok k
  | .Err _ => .Err .InvalidAccountData

theorem caller_error (e : solana_pubkey.PubkeyError) :
    callerMap (.Err e) = .Err .InvalidAccountData := rfl
#print axioms caller_error
end AspisR1.JHs_PDA
end
