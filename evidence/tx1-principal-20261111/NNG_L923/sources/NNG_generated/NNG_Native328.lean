import NNG_Carriers328
import NNG_Lower094
import NMT_328Fold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Native328
open Aeneas Aeneas.Std Result NMT_first NNG_Carriers328

structure Args where
 public_ : Public
 publicBytes : Slice U8
 proof : Slice U8
 k : Usize

def args (a : Args) : NNG_Input094.Args :=
 ⟨toPublic a.public_,LIB_Carriers.bytes a.publicBytes,LIB_Carriers.bytes a.proof,a.k.val⟩
def input (a : NNG_Input094.Args) : Args :=
 ⟨fromPublic a.public_,LIBC_Bytes.raw a.public_bytes,LIBC_Bytes.raw a.proof,LIBC_Usize.raw a.k⟩
theorem args_input (a : NNG_Input094.Args) : args (input a)=NNG_Lower094.lower a := by
 unfold args input NNG_Lower094.lower
 rw [to_from]
#print axioms args_input

def call1 (env : RSL.Env) {H : Type} (_ : aspis_core.digest.Digest32 H)
 (pub : Public) (publicBytes proof : Slice U8) (k : Usize) (_ : H)
 (_ : Option (aspis_r1_cost_probe.verifier.Phase → Result Unit)) :
 Result (core.result.Result (alloc.vec.Vec U8) Error) :=
 NMP_ResultTransport.outer childReply (NNG_Context094.body (NNG_InstalledCalls094.calls env)
  (NNG_Input094.input (args ⟨pub,publicBytes,proof,k⟩) none env))

def call4 (key : solana_hash.Hash) : Result (Array U8 32#usize) := ok key
def call5 (env : RSL.Env) (parts : Slice (Slice U8)) : Result solana_hash.Hash := LIB_Env.hashv env parts
def call6 (_ : Error) : Result solana_program_error.ProgramError := ok .InvalidInstructionData

theorem observer : NMT_first.observer=ok none := rfl
#print axioms observer
/-- Exact runtime partition/reply transport at the caller's actual SDK digest.
The digest value remains the existing Env.sha256 realization. -/
theorem digest_value (env : RSL.Env) (parts : Slice (Slice U8)) :
 (SolanaDigest.Insts.Aspis_coreDigestDigest32 call4 (call5 env)).digest () parts=
 (NNG_PrepareTransport094.digest env).digest () parts := by
 unfold SolanaDigest.Insts.Aspis_coreDigestDigest32 SolanaDigest.Insts.Aspis_coreDigestDigest32.digest call4 call5
  NNG_PrepareTransport094.digest NNG_PublicSource137.digest LIB_VCode.digest
 rw [LIB_Env.hashv_value,bind_tc_ok]
 rfl
#print axioms digest_value

def body (a : Args) (env : RSL.Env) :=
 first_decoded NMT_std_map_err (call1 env) call4 (call5 env) call6 a.public_ a.publicBytes a.proof a.k

/-- Reuse the freshly emitted first_decoded control/std-map fold. -/
theorem source (a : Args) (env : RSL.Env) : body a env=
 (do let r ← call1 env (SolanaDigest.Insts.Aspis_coreDigestDigest32 call4 (call5 env))
       a.public_ a.publicBytes a.proof a.k () none
     match r with
     | .Ok b=>ok (.Ok b)
     | .Err e=>do let pe ← call6 e;ok (.Err pe)) :=
 NMT_emitted_fold (call1 env) call4 (call5 env) call6 a.public_ a.publicBytes a.proof a.k
#print axioms source
end AspisR1.NNG_Native328
