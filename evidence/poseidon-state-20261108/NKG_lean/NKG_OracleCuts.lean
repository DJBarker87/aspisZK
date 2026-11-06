import NKG_OracleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_OracleCuts
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP)
open FJh_Base (State cell)
abbrev Packed := Array NQ 4#usize
abbrev Three := Array NQ 3#usize
abbrev Prepared := Array NP 3#usize
/-- K017–019: one arbitrary fold pre-state, SAME scalar read, exact return. -/
structure Low (l : State) (acc : NQ) (i : Fin 16) (reply out : NQ)
 (args : Fin 2 → NQ) (calls : Nat) : Prop where
 count : calls=1
 left : args 0=acc
 right : args 1=cell l i
 returned : out=reply
/-- K032–034: full raw nine-word cache replies, extensional at every cache word. -/
structure Prepare (w : Three) (theta : NQ) (args : Array NQ 4#usize)
 (replies : Array NP 4#usize) (weights : Prepared) (block : NP) (calls : Nat) : Prop where
 count : calls=4
 inputArgs : ∀ i : Fin 3,cell args ⟨i.val,by have := i.isLt;change i.val<4;omega⟩=cell w i
 blockArg : cell args ⟨3,by decide⟩=theta
 weightsReply : ∀ i : Fin 3,cell weights i=cell replies ⟨i.val,by have := i.isLt;change i.val<4;omega⟩
 blockReply : block=cell replies ⟨3,by decide⟩
/-- K035–037, replacement of retired K023's two-pack prefix. -/
structure Pack (succ internal : State) (g : Fin 4) (inputs : Fin 2 → Packed)
 (replies : Fin 2 → NQ) (target ip : NQ) (calls : Nat) : Prop where
 count : calls=2
 window : ∀ c i,cell (inputs c) i=cell (if c.val=0 then succ else internal)
   ⟨4*g.val+i.val,by have hg := g.isLt;have hi : i.val<4 := i.isLt;change 4*g.val+i.val<16;omega⟩
 targetReply : target=replies 0
 internalReply : ip=replies 1
/-- K038–040: all three source-ordered difference calls and complete reply array. -/
structure Sub (target ip : NQ) (lead full : Packed) (g : Fin 4)
 (args : Fin 3 → Fin 2 → NQ) (replies differences : Three) (calls : Nat) : Prop where
 count : calls=3
 leftArgs : ∀ j,args j 0=target
 rightArgs : ∀ j,args j 1=if j.val=0 then cell lead g else if j.val=1 then cell full g else ip
 returned : differences=replies
/-- K041–043: every prepared-cache word, RHS coordinate and full scalar reply. -/
structure Sum (p logged : Prepared) (differences rhs : Three) (reply out : NQ) (calls : Nat) : Prop where
 count : calls=1
 caches : logged=p
 rightArgs : rhs=differences
 returned : out=reply
/-- K044–046: full prepared block, scalar argument and scalar return. -/
structure Mul (block logged : NP) (sum arg reply out : NQ) (calls : Nat) : Prop where
 count : calls=1
 cache : logged=block
 rightArg : arg=sum
 returned : out=reply
/-- K026–028: the SAME standard constructor, all four indices and outputs. -/
structure Output (replies out : Packed) (indices : Fin 4 → Nat) (calls : Nat) : Prop where
 count : calls=4
 order : ∀ i,indices i=i.val
 returned : out=replies
/-- K029–031: leading/full/internal forwarding on the SAME immutable inputs. -/
structure Prefix (o : FJa_PoseidonOrigins.Openings) (s : FJa_PoseidonOrigins.Selectors)
 (opening : FJa_PoseidonOrigins.Openings) (fullState fullLocal internalState internalLocal : State)
 (leadReply fullReply leadOut fullOut : Packed) (internalReply internalOut : State) (calls : Nat) : Prop where
 count : calls=3
 leadingArgs : opening=o
 fullStateArg : fullState=o.z
 fullLocalArg : fullLocal=s.local
 internalStateArg : internalState=o.z
 internalLocalArg : internalLocal=s.local
 leadingReturn : leadOut=leadReply
 fullReturn : fullOut=fullReply
 internalReturn : internalOut=internalReply
#print Low
#print Prepare
#print Pack
#print Sub
#print Sum
#print Mul
#print Output
#print Prefix
end AspisR1.NKG_OracleCuts
end
