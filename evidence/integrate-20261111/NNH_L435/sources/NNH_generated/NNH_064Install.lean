import NNH_064Observe
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064Install
open Aeneas Aeneas.Std NNH_Libraries
attribute [local instance] Classical.propDecidable

/-- The verifier footprint has no SDK/return-data writes. This frame is used
only to discharge the universally valid frame theorem, never as a physical
headline World or a non-vacuity witness. -/
def frame : NLM_PacketTypes.World Unit :=
 ⟨⟨fun _=>⟨[],[],0,0,false,false,false,0⟩,fun _=>⟨⟨[],0⟩,[],none⟩⟩,[],()⟩

def f064 (pub proof ck : RSL.Bytes) (env : RSL.Env) :
 RSL.Obs (Except V0.VErr Unit) :=
 if h : LIBB_Tx2Auth.Fits pub proof ck then
  NNH_064Execute.observation env (LIB_Bytes.fromBytes pub h.1)
   (LIB_Bytes.fromBytes proof h.2.1) (LIB_Bytes.fromBytes ck h.2.2)
 else ⟨.abort,[]⟩

theorem same (pub proof ck : Slice U8) (env : RSL.Env) :
 f064 (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env=
 NNH_064Execute.observation env pub proof ck := by
 unfold f064
 rw [dif_pos ⟨LIB_Bytes.bytes_bound pub,LIB_Bytes.bytes_bound proof,LIB_Bytes.bytes_bound ck⟩]
 rw [LIB_Bytes.from_bytes,LIB_Bytes.from_bytes,LIB_Bytes.from_bytes]

def install (I0 : RSL.TAS.Impl L V0 VL) : RSL.TAS.Impl L V0 VL :=
 {I0 with f064 := f064}

/-- Concrete TAS NMN field at the canonical library. All source calls and
traces in f064 are computed, and its native witnesses were constructed.
Host association with runtime slots43/44 remains part of literal G0 wiring. -/
theorem refines : RSL.TAS.Refines064 V0 f064 V0.Root0 V0.tx2auth := by
 intro x env domain
 have fits := LIBB_Tx2Auth.fits_of_domain x.1 x.2.1 x.2.2 domain
 unfold f064
 rw [dif_pos fits]
 let pu := LIB_Bytes.fromBytes x.1 fits.1
 let pr := LIB_Bytes.fromBytes x.2.1 fits.2.1
 let cp := LIB_Bytes.fromBytes x.2.2 fits.2.2
 have bytes : (LIB_Carriers.bytes pu,LIB_Carriers.bytes pr,LIB_Carriers.bytes cp)=x := by
  simp only [pu,pr,cp,LIB_Bytes.bytes_from,Prod.mk.eta]
 have exactDomain : RSL.TX2_241.Dom064 V0
  (LIB_Carriers.bytes pu,LIB_Carriers.bytes pr,LIB_Carriers.bytes cp) := bytes ▸ domain
 have folded := NNH_064Observe.canonical env pu pr cp frame exactDomain
 simpa only [pu,pr,cp,LIB_Bytes.bytes_from] using folded

theorem root (I0 : RSL.TAS.Impl L V0 VL) : RSL.TAS.NMN_Root L V0 VL (install I0) :=
 ⟨refines⟩
#print axioms same
#print axioms refines
#print axioms root
end AspisR1.NNH_064Install
