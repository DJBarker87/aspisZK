import NNG_Candidate094
import LIB_ParseShapeTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Reject094
open RSL
abbrev Args := NNG_Input094.Args
abbrev producer := NNG_ProducerFull094.producer

theorem k (a : Args) (env : Env)
 (own : TX1_094.Domain LIB_Instances.VL a none a.public_) (bad : a.k≠SPLIT) :
 producer a none env=⟨.ret (.error LIB_Instances.VL.vParse),[]⟩ := by
 have law := NNG_Candidate094.candidate a none env own
 unfold TX1_094.Ref at law
 have guard : (a.k != SPLIT)=true := by simp [bad]
 rw [guard,RE.check_true,RE.seq_throw] at law
 exact law
#print axioms k

theorem width (a : Args) (env : Env)
 (own : TX1_094.Domain LIB_Instances.VL a none a.public_) (bad : a.proof.length≠57607) :
 producer a none env=⟨.ret (.error LIB_Instances.VL.vParse),[]⟩ := by
 by_cases split : a.k=SPLIT
 · have law := NNG_Candidate094.candidate a none env own
   unfold TX1_094.Ref at law
   have guard : (a.k != SPLIT)=false := by simp [split]
   rw [guard,RE.check_false,RE.seq_pure] at law
   have parsed : ∀ o,LIB_Instances.VL.parseShape.run a.proof env o ↔
    o=⟨.ret (.error LIB_Instances.VL.vParse),[]⟩ := fun o=>LIB_ParseShapeTotal.rejected a.proof env bad o
   unfold RE.seq at law
   rw [RE.bind,Spec.bind_det _ _ env _ parsed] at law
   exact law
 · exact k a env own split
#print axioms width
end AspisR1.NNG_Reject094
