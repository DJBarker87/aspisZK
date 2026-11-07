import NMC_FrameProjections
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Frame
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
theorem challenge_ext (a b : r1_wire.Challenges)
 (h0 : a.lambda=b.lambda) (h1 : a.chi=b.chi) (h2 : a.theta=b.theta)
 (h3 : a.zc=b.zc) (h4 : a.mu=b.mu) (h5 : a.eta=b.eta) : a=b := by
 cases a;cases b;cases h0;cases h1;cases h2;cases h3;cases h4;cases h5;rfl
theorem owned_ext (a b : NMC_Parent.OwnedClaims)
 (id : a.identity=b.identity) (value : a.value=b.value) : a=b := by
 cases a;cases b;cases id;cases value;rfl
theorem point_ext (a b : NLC_Finish.Point) (x : a.x=b.x) (y : a.y=b.y) : a=b := by
 cases a;cases b;cases x;cases y;rfl
theorem transcript_ext (a b : r1_wire.SemanticTranscript Unit)
 (state : a.state=b.state) (next : a.next_row=b.next_row) : a=b := by
 cases a with
 | mk s h n=>cases b with
   | mk t k m=>cases state;cases next;cases h;cases k;rfl
theorem value_ext (a b : Value)
 (h0 : a.running=b.running) (h1 : a.alpha=b.alpha) (h2 : a.transcript=b.transcript)
 (h3 : a.challenges=b.challenges) (h4 : a.claims=b.claims) (h5 : a.terminal=b.terminal)
 (h6 : a.mask=b.mask) (h7 : a.extra=b.extra) (h8 : a.before=b.before)
 (h9 : a.state=b.state) (h10 : a.z0=b.z0) (h11 : a.z1=b.z1)
 (h12 : a.rest=b.rest) (h13 : a.reservation=b.reservation) : a=b := by
 cases a;cases b;cases h0;cases h1;cases h2;cases h3;cases h4;cases h5;cases h6
 cases h7;cases h8;cases h9;cases h10;cases h11;cases h12;cases h13;rfl
/-- Complete explicit parent record, including the live allocation's identity
AND its payload, rest heap, allocator reservation and all local values.
This reassembly theorem gives no native credit until every selector law is
supplied by the actual segment and its matched failing controls. -/
theorem complete (a b : Value) (same : Same a b) : a=b := by
 exact value_ext a b (running a b same) (alpha a b same)
  (transcript_ext _ _ (transcript_state a b same) (transcript_next a b same))
  (challenge_ext _ _ (challenges_lambda a b same) (challenges_chi a b same)
   (challenges_theta a b same) (challenges_zc a b same) (challenges_mu a b same) (challenges_eta a b same))
  (owned_ext _ _ (claims_identity a b same) (claims_value a b same))
  (terminal a b same) (mask a b same) (extra a b same) (before a b same)
  (state a b same) (point_ext _ _ (z0_x a b same) (z0_y a b same))
  (point_ext _ _ (z1_x a b same) (z1_y a b same)) (rest a b same) (reservation a b same)
#print axioms challenge_ext
#print axioms owned_ext
#print axioms point_ext
#print axioms transcript_ext
#print axioms value_ext
#print axioms complete
set_option pp.proofs false in #print complete
end AspisR1.NMC_Frame
end
