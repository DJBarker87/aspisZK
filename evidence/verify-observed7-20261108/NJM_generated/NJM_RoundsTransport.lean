import NJM_TranscriptFrame
set_option autoImplicit false
namespace AspisR1.NJM_RoundsTransport
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames NJG_RoundsCode

/-- Native ABI projection; every Rust error constructor is preserved. -/
def lower {H : Type} : Output H → RoundOutput
 | .Err e=>.Err e
 | .Ok (running,alpha,t)=>.Ok (running,alpha,t.state,t.next_row)

def raise {H : Type} (hash : H) : RoundOutput → Output H
 | .Err e=>.Err e
 | .Ok (running,alpha,state,next)=>.Ok (running,alpha,{state:=state,hash:=hash,next_row:=next})

def Frame {H : Type} (hash : H) : Output H → Prop
 | .Err _=>True
 | .Ok (_,_,after)=>after.hash=hash

/-- Equality of state/next windows is sufficient only after proving the
remaining hash carrier frame from the original child source. -/
theorem roundtrip {H : Type} (hash : H) (reply : Output H) (frame : Frame hash reply) :
 raise hash (lower reply)=reply := by
 cases reply with
 | Err e=>rfl
 | Ok pair=>
   rcases pair with ⟨running,alpha,after⟩
   cases after with
   | mk state afterHash next=>
     change afterHash=hash at frame
     subst afterHash
     rfl

/-- The source round supplies the full ABI carrier frame on every returning
arm. This is derived at the SAME call, not supplied as an endpoint premise. -/
theorem source_frame {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (carry : Carry H) (r : Usize) (bound : r.val<10) (reply : Output H)
 (call : (PreparedHashCode.run (S1SemanticCode.roundStep NJM_RoundJoin.R D pre carry.2.2 carry.2.1 carry.1 r)).2=ok reply) :
 Frame carry.2.2.hash reply := by
 cases reply with
 | Err e=>trivial
 | Ok pair=>
   rcases pair with ⟨value,next,after⟩
   exact NJM_TranscriptFrame.round D pre carry.2.2 after carry.2.1 next carry.1 value r bound call

#print axioms roundtrip
#print axioms source_frame
end AspisR1.NJM_RoundsTransport
