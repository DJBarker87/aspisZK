import NIT_RegularChain
import NIT_RefInterpretation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_EdgeInstantiation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIT_RefInterpretation
variable [FIo_Native.Allocation]

/-- A returning regular child, including Err, establishes PairEdges' canonical
post-state from the SAME vector/Parts inputs. No regular success is presumed. -/
theorem regular (c : Context) (b : Bool) (before after : Scratch) (reply : RU) (parts : Parts)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (inv : NHX_RegularPost.Inv before initial)
 (call : FIo_Native.weights.process_regular_kinds c.w.value b c.alpha.value.to_slice c.f.value
  2#usize 64#usize c.ap0.value c.ap1.value before initial=ok (reply,after,parts))
 (common : Ref CommonCells) (partials : Powers) (partialCanonical : canonical partials)
 (power i : Nat) (hp : power<4) (hi : i<16) :
 ∃ l : PairEdges,
 cutPairEdges c.w c.alpha c.f
  ⟨c.scratchAddress,⟨(alloc.vec.Vec.deref before).val,inv.2.1⟩⟩
  ⟨c.partsAddress,initial⟩ c.ap0.value c.ap1.value common b power i l ∧
 l.regular_post=parts ∧ l.partial_reply=partials ∧
 decode c.w l.who=some c.w.value ∧ decode c.alpha l.alpha=some c.alpha.value ∧
 decode c.f l.message=some c.f.value := by
 have post := NIG_PairFrames.regular c.w.value b c.alpha.value.to_slice c.f.value c.ap0.value c.ap1.value
  domain.s2 domain.factors c0 c1 before after initial parts reply inv call
 let scratch : Ref (Array K 64#usize) := ⟨c.scratchAddress,⟨(alloc.vec.Vec.deref before).val,inv.2.1⟩⟩
 let initialParts : Ref Parts := ⟨c.partsAddress,initial⟩
 obtain ⟨l,cut,regularPost,partialReply⟩ := NIT_ControlCuts.edges c.w c.alpha c.f scratch initialParts
  c.ap0.value c.ap1.value common b power i parts partials domain.s2
  (NIT_PairDomain.message_size _ _ _ _ domain) domain.alphas c0 c1 inv.2.2 post.2.2 partialCanonical hp hi
 obtain ⟨owner,alpha,message,_,_⟩ := regular_arguments c.w c.alpha c.f scratch initialParts c.ap0.value c.ap1.value common b power i l cut
 exact ⟨l,cut,regularPost,partialReply,owner,alpha,message⟩

/-- This canonical reply fact comes from the CLOSED partials packet at the
actual bytes/common input; it is not a stronger caller precondition. -/
theorem partials (f : Slice U8) (common : CommonCells) (reply : Powers)
 (call : FIo_Native.weights.shared_partials f common=ok (.Ok reply)) : canonical reply :=
 NIG_PairFrames.partials f common reply call

#print axioms regular
#print axioms partials
end AspisR1.NIT_EdgeInstantiation
