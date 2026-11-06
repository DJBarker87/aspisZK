import NLC_FinishState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code)
/-- Missing slots are an explicit interpreter fault, never a chosen successful value.
The source-initialization proof must exclude this fault before native credit. -/
def read {A : Type} : Option A → Result A
 | some a => ok a
 | none => fail .panic

def returned {A H : Type} (s : State H) (e : Event)
 (r : core.result.Result A r1_wire.Error) (store : A → Locals H) : Post H :=
 match r with
 | .Ok a => .inr (put s e (store a))
 | .Err err => .inl (.Err err)
/-- Fixed deployed semantic calls, with no free operation dictionary or selected reply.
This defines source steps only. Native cut installation is a separate obligation. -/
def step {H : Type} (s : State H) : Code (Post H) := do
 let i := s.input
 let l := s.locals
 match s.next with
 | .rounds =>
   let r ← S1SemanticCode.rounds NJM_RoundJoin.R i.digest i.prefix1 i.transcript
   pure (returned s .mark2 r (fun v => {l with running:=some v.1, alpha:=some v.2.1, transcript:=some v.2.2}))
 | .mark2 =>
   VerifyPrefix.mark none 2#u8
   pure (.inr (setNext s .claims))
 | .claims =>
   let r ← (IDa_Deployed.boundaries i.reservation).claims i.prefix1
   pure (returned s .original r (fun v => {l with claims:=some v}))
 | .original => pure (.inr (setNext s .terminal))
 | .terminal =>
   let c ← read l.claims
   let a ← read l.alpha
   let r ← (IDa_Deployed.boundaries i.reservation).terminal i.publicValue c a i.challenges
   pure (.inr (put s .mapPublic {l with terminalReply:=some r}))
 | .mapPublic =>
   let r ← read l.terminalReply
   let r1 ← core.result.Result.map_err (FinishModel.closureFn11 i.digest) r ()
   pure (returned s .mark3 r1 (fun v => {l with terminal:=some v}))
 | .mark3 =>
   VerifyPrefix.mark none 3#u8
   pure (.inr (setNext s .lowArray))
 | .lowArray =>
   let c ← read l.claims
   let low ← (IDa_Deployed.boundaries i.reservation).fromFn 16#usize (FinishModel.closureFn9 i.digest) c
   pure (.inr (put s .highArray {l with low:=some low}))
 | .highArray =>
   let c ← read l.claims
   let high ← (IDa_Deployed.boundaries i.reservation).fromFn 10#usize (FinishModel.closureFn5 i.digest) c
   pure (.inr (put s .blind {l with high:=some high}))
 | .blind =>
   let c ← read l.claims
   let row ← Array.index_usize c 0#usize
   let blind ← Array.index_usize row 27#usize
   pure (.inr (put s .alpha {l with blind:=some blind}))
 | .alpha => pure (.inr (setNext s .mask))
 | .mask =>
   let low ← read l.low
   let high ← read l.high
   let blind ← read l.blind
   let alpha ← read l.alpha
   let mask ← (IDa_Deployed.boundaries i.reservation).mask low high blind alpha
   pure (.inr (put s .record25a {l with mask:=some mask}))
 | .record25a =>
   let r ← r1_wire.Prefix.validated_record i.prefix1 25#u8
   pure (returned s .decode25 r (fun v => {l with record25:=some v}))
 | .decode25 =>
   let record ← read l.record25
   let r ← NJM_RoundJoin.R.decode 29#usize record 87#usize
   pure (returned s .multiply r (fun v => {l with extra:=some v}))
 | .multiply =>
   let terminal ← read l.terminal
   let product ← (IDa_Deployed.boundaries i.reservation).mul i.challenges.eta terminal
   pure (.inr (put s .addMask {l with product:=some product}))
 | .addMask =>
   let mask ← read l.mask
   let product ← read l.product
   let v ← (IDa_Deployed.boundaries i.reservation).add mask product
   pure (.inr (put s .extra28 {l with partialValue:=some v}))
 | .extra28 =>
   let extra ← read l.extra
   let v ← Array.index_usize extra 28#usize
   pure (.inr (put s .addExtra {l with extraCell:=some v}))
 | .addExtra =>
   let x ← read l.partialValue
   let y ← read l.extraCell
   let masked ← (IDa_Deployed.boundaries i.reservation).add x y
   pure (.inr (put s .terminalGuard {l with masked:=some masked}))
 | .terminalGuard =>
   let running ← read l.running
   let masked ← read l.masked
   let reject ← core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running masked
   if reject then pure (.inl (.Err r1_wire.Error.Terminal))
   else pure (.inr (setNext s .mark4))
 | .mark4 =>
   VerifyPrefix.mark none 4#u8
   pure (.inr (setNext s .stateBefore))
 | .stateBefore =>
   let t ← read l.transcript
   let v ← r1_wire.SemanticTranscript.impl.state i.digest t
   pure (.inr (put s .record25b {l with stateBefore:=some v}))
 | .record25b =>
   let r ← r1_wire.Prefix.validated_record i.prefix1 25#u8
   pure (returned s .circle0 r (fun v => {l with record25:=some v}))
 | .circle0 =>
   let t ← read l.transcript
   let rec ← read l.record25
   let (r,t1) ← S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest t rec
   pure (returned s .record26a r (fun v => {l with z0:=some v, transcript:=some t1}))
 | .record26a =>
   let r ← r1_wire.Prefix.validated_record i.prefix1 26#u8
   pure (returned s .decode26 r (fun v => {l with record26:=some v}))
 | .decode26 =>
   let rec ← read l.record26
   let r ← NJM_RoundJoin.R.decode 29#usize rec 0#usize
   pure (returned s .record26b r (fun v => {l with beforeZ1:=some v}))
 | .record26b =>
   let r ← r1_wire.Prefix.validated_record i.prefix1 26#u8
   pure (returned s .circle1 r (fun v => {l with record26:=some v}))
 | .circle1 =>
   let t ← read l.transcript
   let rec ← read l.record26
   let (r,t1) ← S1SemanticCode.circleValidated (IDa_Deployed.boundaries i.reservation) i.digest t rec
   pure (returned s .mark5 r (fun v => {l with z1:=some v, transcript:=some t1}))
 | .mark5 =>
   VerifyPrefix.mark none 5#u8
   pure (.inr (setNext s .circleGuard))
 | .circleGuard =>
   let z0 ← read l.z0
   let z1 ← read l.z1
   let reject ← FinishModel.pointEq z0 z1
   if reject then pure (.inl (.Err r1_wire.Error.EqualCirclePoints))
   else pure (.inr (setNext s .payload2))
 | .payload2 =>
   let r ← FinishModel.payload i.prefix1 2#u8
   pure (returned s .rootCopy r (fun v => {l with payload:=some v}))
 | .rootCopy =>
   let payload ← read l.payload
   let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 payload
   let root ← (IDa_Deployed.boundaries i.reservation).unwrapRoot r
   pure (.inr (put s .verified {l with root:=some root}))
 | .verified =>
   let root ← read l.root
   let alpha ← read l.alpha
   let claims ← read l.claims
   let extra ← read l.extra
   let beforeZ1 ← read l.beforeZ1
   let stateBefore ← read l.stateBefore
   let z0 ← read l.z0
   let z1 ← read l.z1
   let transcript ← read l.transcript
   pure (.inl (.Ok {roots:=Array.make 2#usize [i.prefix1.c1_root,root],challenges:=i.challenges,
     alpha,claims,extra,before_z1:=beforeZ1,state_before_z0:=stateBefore,
     z:=Array.make 2#usize [z0,z1],transcript}))
 | .lowIndex | .highIndex => liftM (fail .panic)
end AspisR1.NLC_Finish
end
