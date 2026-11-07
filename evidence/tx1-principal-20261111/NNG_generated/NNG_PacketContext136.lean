import NNG_Producer136
import NNG_AllReached136
import NNG_DOccurrenceLaws136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PacketContext136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_Representation136 NNG_TraceAll136 NNG_TypedDomains136

theorem public_domain (a : Args) (domain : RSL.TX1_136.Domain VL a) : LIB_VPublicDomain.publicDom a.public_ :=
  ⟨domain.1,domain.2.1⟩
#print axioms public_domain

theorem checked (a : Args) (obs : RSL.Observer) (env : RSL.Env) (domain : RSL.TX1_136.Domain VL a) :
    All Checked (NNG_FinishTree.tree (calls a env) (input a obs env)) :=
  NNG_AllReached136.all_calls env a.public_ a.prefix_ a.transcript a.challenges (observer obs) (public_domain a domain)
#print axioms checked

theorem orig_identity (c : LIB_VCarriers.Challenges) : LIB_VCarriers.origChallenges c=c := by cases c;rfl
#print axioms orig_identity
end AspisR1.NNG_PacketContext136
