import NKU_FineRoots
import NKU_FineGamma
import NKU_FineZ
import NKU_FineQueryFirst
import NKU_FineQueryMid
import NKU_FineQueryEnd
import NKU_ResumeRoot
set_option autoImplicit false
noncomputable section
namespace NKU_Fold
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
abbrev Occurrence := NJU_ResumeObserved.Event
def z {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_FineZ.run s
 NKK_Try.emitted reply (fun (_,post)=>NKU_AfterZ.run d post)
def semantic {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_Semantic.run s
 NKK_Try.emitted reply (fun (_,post)=>z d post)
def lastQuery {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_FineQueryEnd.run s
 NKK_Try.emitted reply fun (_,post)=>do
 let valid ← NKU_Validator.run post
 NKK_Try.emitted valid (fun (_,checked)=>semantic d checked)
def middleQuery {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_FineQueryMid.run s
 NKK_Try.emitted reply (fun (_,post)=>lastQuery d post)
def firstQuery {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_FineQueryFirst.run s
 NKK_Try.emitted reply (fun (_,post)=>middleQuery d post)
def gamma {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_FineGamma.run s
 NKK_Try.emitted reply (fun (_,post)=>firstQuery d post)
def roots {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_FineRoots.run s
 NKK_Try.emitted reply (fun (_,post)=>gamma d post)
def digest {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (s : NKU.State) (next : U8) («end» : Usize) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_DigestJoin.run d hash «end» s
 NKK_Try.emitted reply (fun (_,post)=>roots d (NKU_HeaderSlots.set post next «end»))
def suffix {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) :=
 match s.decoded.next,s.decoded.endAt with
 | some next,some «end» => digest d hash s next «end»
 | _,_ => liftM (Result.fail .panic)
/-- One chronological fold over every resume occurrence. Within the native
read windows the SAME parent State is updated after EACH raw/E/K call. -/
def G {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (s : NKU.State) : Run (core.result.Result NKU.Pair verifier.Error) := do
 let reply ← NKU_HeaderStep.run d s
 NKK_Try.emitted reply (fun (_,post)=>suffix d hash post)
end NKU_Fold
