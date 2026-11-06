import NJP_DigestCarrier
import MultiproofConePhysicalDigest

set_option autoImplicit false
noncomputable section
namespace NJP_RequestTransport
open Aeneas Aeneas.Std Result NJP_RowModel NJP_DigestCarrier
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
abbrev Address := Slice (Slice U8)

def address (request : Request) : Address :=
 AspisR1.MultiproofConePhysicalDigest.parts (encode request.1) (encode request.2)

def hash (H : Address → RefDigest) (request : Request) : Digest := decode (H (address request))

/-- Exact query/reply representation change, preserving every chronological
request, repeated request and rejected prefix. No query is deduplicated. -/
def transport {α : Type} : Program Request Digest α → Program Address RefDigest α
 | .done x => .done x
 | .ask request next => .ask (address request) fun answer => transport (next (decode answer))

theorem observation {α : Type} (H : Address → RefDigest) (p : Program Request Digest α) :
 eval H (transport p)=
 ((eval (hash H) p).1.map (fun event => (address event.1,encode event.2)),(eval (hash H) p).2) := by
 induction p with
 | done x => rfl
 | ask request next ih =>
   simp only [transport,eval,hash,ih,List.map_cons,encode_decode]

theorem prefix_map (H : Address → RefDigest) (history : List (Request × Digest)) (n : Nat) :
 (history.take n).map (fun event => (address event.1,encode event.2))=
   (history.map (fun event => (address event.1,encode event.2))).take n := by
 rw [List.map_take]

#print observation
#print axioms observation
#print prefix_map
#print axioms prefix_map
end NJP_RequestTransport
end
