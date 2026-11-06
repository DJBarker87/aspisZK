import NIX_ValidatedCut
import NIX_CircleLogLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_Cuts
open Aeneas Aeneas.Std Result
open AspisR1CircleSampleWrapper
abbrev Q := field.QM31
abbrev P := circle.SecureCirclePoint
abbrev E := circle.CirclePointError
structure SamplerPre (Pointer : Type) where
 block : Array U8 32#usize
 pointer : Pointer
 row : r0_transcript.CircleRow
 parameter : Q
 mapped : core.result.Result P E
 fallback : P
 oldIndex : Nat
 count : Nat
 at2 : Nat
 frame : Nat
structure SamplerPost (Pointer : Type) where
 pointer : Pointer
 parameter : Q
 index : Nat
 count : Nat
 at0 : Nat
 at1 : Nat
 at2 : Nat
 frame : Nat
 result : P

def rowIndex (row : r0_transcript.CircleRow) : Nat := match row with | .First=>0 | .Second=>1

def needsFallback (r : core.result.Result P E) : Bool := match r with | .Ok _=>false | .Err _=>true

def chosen {Pointer : Type} (s : SamplerPre Pointer) : P := match s.mapped with | .Ok p=>p | .Err _=>s.fallback

/-- NIX_sampler.rs.txt SHA256 bf3862dcb456c8c0713a2635761194ff9cbc0448d24afdc14bae995bb3a47dbb, K053/K048.
Transcribes assertions: log.block==block.as_ptr(), same(log.parameter,q),
log.index==row index iff Err else old_index; at[0]=count, at[1]=count+1,
at[2]=count+2 iff Err else old at[2], count+=3 iff Err else +=2;
log.frame==frame; same(result.x,expected.x)&&same(result.y,expected.y).
Native preconditions: canonical(q) and count<253. Pointer is the SAME borrowed
block token under retained Rust borrow interpretation; no point-value law is added. -/
def samplerCut {Pointer : Type} (s : SamplerPre Pointer) (p : SamplerPost Pointer) : Prop :=
 AspisV8R19.SamplerClosureProductCorrectness.Canonical (toR72QM s.parameter) ∧ s.count<253 ∧
 p.pointer=s.pointer ∧ p.parameter=s.parameter ∧
 p.index=(if needsFallback s.mapped then rowIndex s.row else s.oldIndex) ∧
 p.at0=s.count ∧ p.at1=s.count+1 ∧
 p.at2=(if needsFallback s.mapped then s.count+2 else s.at2) ∧
 p.count=s.count+(if needsFallback s.mapped then 3 else 2) ∧
 p.frame=s.frame ∧ p.result=chosen s

/-- Instantiates callee laws on the same block/row/parameter. These are callee
reply equations, not a successful sampler/caller premise. -/
theorem sampler_compose {Pointer : Type} (s : SamplerPre Pointer) (p : SamplerPost Pointer)
 (cut : samplerCut s p)
 (sample : sampler.qm31_sample s.block=ok s.parameter)
 (map : _root_.circle.secure_ood_circle_point_from_parameter s.parameter=ok s.mapped)
 (fallback : s.fallback=NIX_FallbackLaw.expected s.row) :
 sampler.circle_sample s.block s.row=ok p.result := by
 have result : p.result=chosen s:=cut.2.2.2.2.2.2.2.2.2.2
 rw [result]
 have law:=NIX_SamplerLaw.source_of_log s.block s.row s.parameter s.mapped sample map
 cases m : s.mapped <;> simpa only [chosen,NIX_SamplerLaw.reply,m,fallback] using law

/-- Complete SAME-block packet supplies the cut's opaque replies and their domain.
No result, Run, output-success, endpoint equality or caller-success premise. -/
theorem sampler_replies (block : Array U8 32#usize) (row : r0_transcript.CircleRow) :
 ∃ q mapped,
 sampler.qm31_sample block=ok q ∧
 AspisV8R19.SamplerClosureProductCorrectness.Canonical (toR72QM q) ∧
 _root_.circle.secure_ood_circle_point_from_parameter q=ok mapped ∧
 _root_.transcript.circle_fallback_point (NIX_FallbackLaw.index row)=ok (NIX_FallbackLaw.expected row) := by
 obtain ⟨q,mapped,sample,domain,map,_⟩:=NIX_SamplerLaw.packet block row
 exact ⟨q,mapped,sample,domain,map,NIX_FallbackLaw.deployed row⟩

#print axioms sampler_compose
#print axioms sampler_replies
end AspisR1.NIX_Cuts
end
