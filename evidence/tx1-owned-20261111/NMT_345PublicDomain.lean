import NMT_345TransitionDomains
import NMT_345FIq_T5
import NMT_345Semantic
import NMT_345MapOk
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result AspisR1
/-- Exact NLS-bf:TX1:136:TX1:256:hd on the same semantic public. -/
def publicDomain (p : Public) : Prop :=
 NKR_DigestChildren.Domain (NKR_TermPublic.value (NMT_345FIq.toT5 p))

theorem validated_public_domain (s : Statement) (good : validateCall s = .ok (.Ok ())) :
 publicDomain (semanticValue s) := by
 have native : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
   (NMT_345Dec.toT8 s) = .ok (.Ok ()) := by
  exact map_ok_recover NMT_345Dec.fromT13 _ () good
 have hp := payment_domains (NMT_345Dec.toT8 s) native
 have ht := transition_domains (NMT_345Dec.toT8 s) native
 cases s with
 | PrivateTransfer c p =>
  dsimp only [PaymentDomains,NMT_345Dec.toT8,NMT_345Dec.toT3] at hp
  dsimp only [TransitionDomains,NFY_NBN_StatementResult.common,NBD_TerminalProjection.common,
    NMT_345Dec.toT8,NMT_345Dec.toT7,NMT_345Dec.toT6,NMT_345Dec.toT4,NMT_345Dec.toT5] at ht
  unfold publicDomain semanticValue
  refine ⟨hp.1,hp.2.1,?_,hp.2.2.2,ht.1,ht.2.1,ht.2.2⟩
  intro d hd
  have e : p.recipient_commitment = d := Option.some.inj hd
  subst d
  exact hp.2.2.1
 | Withdrawal c p =>
  dsimp only [PaymentDomains,NMT_345Dec.toT8,NMT_345Dec.toT2] at hp
  dsimp only [TransitionDomains,NFY_NBN_StatementResult.common,NBD_TerminalProjection.common,
    NMT_345Dec.toT8,NMT_345Dec.toT7,NMT_345Dec.toT6,NMT_345Dec.toT4,NMT_345Dec.toT5] at ht
  unfold publicDomain semanticValue
  refine ⟨hp.1,hp.2.1,?_,hp.2.2,ht.1,ht.2.1,ht.2.2⟩
  intro d hd
  cases hd
#print axioms validated_public_domain
end NMT_345
