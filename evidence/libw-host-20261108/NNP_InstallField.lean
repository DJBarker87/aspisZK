import NNP_HostIdentity
import NNP_SeparateHeader
import NNH_064World
set_option autoImplicit false
noncomputable section
namespace NNP_InstallField
open AspisR1

/-- The separate-header predicate is precisely the merged host predicate. -/
theorem header_identity : NNP_SeparateHeader.header = NNH_G1aEnv.header := rfl

/-- Re-specialise the already merged concrete host field at its exact signature. -/
def field (S : RSL.TAS.Sig)
 (I0 : RSL.TAS.Impl NNH_Libraries.L LIBB_V2Star.library NNH_Libraries.VL) :
 RSL.TAS.NNC_G1a (NNH_G1aEnv.sig S) NNH_Libraries.L LIBB_V2Star.library
  NNH_Libraries.VL (NNH_064Install.install I0) := NNH_G1aEnv.field S I0

theorem field_law (S : RSL.TAS.Sig)
 (I0 : RSL.TAS.Impl NNH_Libraries.L LIBB_V2Star.library NNH_Libraries.VL) :
 (field S I0).w = LIBW_WeakPerEnv.wEnv NNH_064Install.frame := rfl

/-- Native annotations may be rebuilt at a different caller frame. End and
trace are retained, so the weak observed law does not gain or lose an outcome. -/
theorem transport {A B : Type} (before : NLM_PacketTypes.World A)
 (after : NLM_PacketTypes.World B) (pub proof ck : RSL.Bytes) (env : RSL.Env)
 (o : RSL.Obs (Except LIBW_WeakPerEnv.LibErr Unit))
 (h : LIBW_WeakPerEnv.wEnv before pub proof ck env o) :
 LIBW_WeakPerEnv.wEnv after pub proof ck env o := by
 obtain ⟨pu,pr,cp,hpu,hpr,hcp,outcome,events,trace,native,source,same⟩ := h
 obtain ⟨next,hn⟩ := NNH_064World.transport (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pu,pr,cp,()⟩,before⟩ after outcome events native
 exact ⟨pu,pr,cp,hpu,hpr,hcp,outcome,next,trace,hn,source,same⟩

theorem world_independent {A B : Type} (before : NLM_PacketTypes.World A)
 (after : NLM_PacketTypes.World B) :
 LIBW_WeakPerEnv.wEnv before = LIBW_WeakPerEnv.wEnv after := by
 funext pub proof ck env o
 apply propext
 exact ⟨transport before after pub proof ck env o,transport after before pub proof ck env o⟩

theorem any_host_law : LIBW_WeakPerEnv.wAny Unit = NNH_064WeakField.w := by
 rw [←NNP_HostIdentity.host_law]
 funext pub proof ck env o
 apply propext
 constructor
 · rintro ⟨world,h⟩
   exact transport world NNH_064Install.frame pub proof ck env o h
 · intro h
   exact ⟨NNH_064Install.frame,h⟩

#print axioms header_identity
#print axioms field
#print axioms field_law
#print axioms transport
#print axioms world_independent
#print axioms any_host_law
end NNP_InstallField
