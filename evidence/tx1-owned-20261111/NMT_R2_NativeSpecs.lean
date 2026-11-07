import NMT_R2_ReachLibrary
import NMT_R2_EmittedData
import NMT_R2_ResultTry
set_option autoImplicit false
noncomputable section
namespace NMT_R2_NativeSpecs
open Aeneas Aeneas.Std NMT_345 RSL

structure Args345 where
 program : Key
 accounts : Slice Account
 data : Slice U8

def args345 (a : Args345) : NMT_R2.TX1_345.Args :=
 ⟨key a.program,a.accounts.val.map account,a.data.val.map byte⟩

structure Args328 where
 public_ : Public
 public_bytes : Slice U8
 proof : Slice U8
 k : Usize

def args328 (V : VLib) (encodePublic : Public → V.Public) (a : Args328) :
 NMT_R2.TX1_328.Args (NMT_R2_PublicLibrary.withPublic V encodePublic) :=
 ⟨a.public_,a.public_bytes.val.map byte,a.proof.val.map byte,a.k.val⟩

def observation (o : Obs (core.result.Result (alloc.vec.Vec U8) PE)) : Obs (Except ProgramError Bytes) :=
 ⟨match o.exit with
  | .ret r => .ret (rustResult (fun b => b.val.map byte) r)
  | .abort => .abort
  | .diverge => .diverge,o.events⟩

/-- Native-carrier form of the FULL canonical328 packet. All original typed
arguments and every Result, event and stopped prefix are retained. The exact
carrier difference from the List/Nat specification is documented separately. -/
def RowSpec328 (V : VLib) (encodePublic : Public → V.Public)
 (P : PreparedNew (NMT_R2_PublicLibrary.withPublic V encodePublic))
 (impl : Args328 → Env → Obs (core.result.Result (alloc.vec.Vec U8) PE)) : Prop :=
 ∀ a env, publicDomain a.public_ →
 NMT_R2.TX1_328.Ref (NMT_R2_PublicLibrary.withPublic V encodePublic) P
  (args328 V encodePublic a) env (observation (impl a env))

def RowSpec345 (V : VLib) (encodePublic : Public → V.Public)
 (P : PreparedNew (NMT_R2_PublicLibrary.withPublic V encodePublic))
 (impl : Args345 → Env → Obs (core.result.Result (alloc.vec.Vec U8) PE)) : Prop :=
 ∀ a env, NMT_R2.TX1_345.Ref (NMT_R2_PublicLibrary.withPublic V encodePublic) P
  (NMT_R2_ReachLibrary.library V encodePublic) (args345 a) env (observation (impl a env))

/-- Forward instantiation of the canonical packet, with a total, all-outcome
representation equation. No child-success or endpoint premise is used. -/
theorem child_from_canonical (V : VLib) (encodePublic : Public → V.Public)
 (P : PreparedNew (NMT_R2_PublicLibrary.withPublic V encodePublic))
 (canonical : NMT_R2.TX1_328.Args (NMT_R2_PublicLibrary.withPublic V encodePublic) → Env → Obs (Except ProgramError Bytes))
 (native : Args328 → Env → Obs (core.result.Result (alloc.vec.Vec U8) PE))
 (packet : NMT_R2.TX1_328.RowSpec_328 (NMT_R2_PublicLibrary.withPublic V encodePublic) P canonical)
 (representation : ∀ a env, observation (native a env) = canonical (args328 V encodePublic a) env) :
 RowSpec328 V encodePublic P native := by
 intro a env domain
 rw [representation]
 exact packet _ env domain
#print axioms child_from_canonical
end NMT_R2_NativeSpecs
end
