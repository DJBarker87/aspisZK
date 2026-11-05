from pathlib import Path
import hashlib
E=Path(__file__).resolve().parent
old=E/'NIY_K045/sources/NIY_src/crates/aspis-r1-cost-probe/src/NIY_scan_native.rs';current=E/'NIY_scan_native.rs.txt'
a=hashlib.sha256(old.read_bytes()).hexdigest();b=hashlib.sha256(current.read_bytes()).hexdigest()
s='''import NIY_NativeFinalCuts
set_option autoImplicit false
noncomputable section
namespace NIY_ScanCuts
open Aeneas Aeneas.Std NIL_Carriers NIY_NativeCuts
abbrev Reply := core.result.Result Unit Cohort.Err

def step (reply rest : Reply) : Reply :=
 match reply with
 | .Ok () => rest
 | .Err err => .Err err

def chain (reply : Fin 4 → Reply) (tail : Reply) : Reply :=
 step (reply ⟨0,by decide⟩) (step (reply ⟨1,by decide⟩)
   (step (reply ⟨2,by decide⟩) (step (reply ⟨3,by decide⟩) tail)))

def calls (reply : Fin 4 → Reply) : Nat :=
 match reply ⟨0,by decide⟩ with
 | .Err _ => 1
 | .Ok () => match reply ⟨1,by decide⟩ with
   | .Err _ => 2
   | .Ok () => match reply ⟨2,by decide⟩ with
     | .Err _ => 3
     | .Ok () => 4

def expectedLength (i : Fin 4) : Nat :=
 match i.val with | 0=>464 | 1=>32 | 2=>224 | _=>2272

/-- NIY_K045/sources/NIY_src/crates/aspis-r1-cost-probe/src/NIY_scan_native.rs,
SHA256 PREFIXHASH. "assert_eq!(ptr,self.proof[start..end].as_ptr() as usize);"
"assert_eq!(bytes.len(),end-start);assert_eq!(mode,if c==0{None}else{Some(false)});"
"assert_eq!(log.calls,if !ok[0]{1}else if !ok[1]{2}else if !ok[2]{3}else{4});"
"assert_eq!(result,expected);". Addresses are observations of expected slices;
this definition does NOT turn address equality into byte equality or a full scan.
It is only the returning four-call prefix, with an arbitrary tail Result. -/
def prefixCut (expected : Fin 4 → Nat) (received : Fin 4 → NIY_NativeFinalCuts.Descriptor)
 (mode : Fin 4 → Option Bool) (reply : Fin 4 → Reply) (tail returned : Reply)
 (count : Nat) : Prop :=
 count=calls reply ∧
 (∀ i : Fin 4,i.val<count → received i |>.address = expected i ∧
   (received i).length=expectedLength i ∧ mode i=(if i.val=0 then none else some false)) ∧
 returned=chain reply tail

/-- Same pinned PREFIXHASH source. M31 step assertions:
"assert_eq!(current,l);assert_eq!(range.len(),25-l);"
"assert_eq!(actual.is_ok(),expected^cfg!(NIY_invert));"
"if let Err(error)=actual{assert_eq!(error,Error::Parse);}".
Exit: "assert_eq!(l,26);assert_eq!(range.len(),0);". Positive configuration only. -/
def m31Cut (q : Slice U8) (s : Fin 4) (l : Fin 27) (current remaining : Nat)
 (returned : Option Reply) : Prop :=
 match returned with
 | none => l.val=26 ∧ remaining=0
 | some reply => l.val<26 ∧ current=l.val ∧ remaining=25-l.val ∧
     match reply with
     | .Ok () => wordAt q (s.val*120+l.val*4)<2147483647
     | .Err err => ¬wordAt q (s.val*120+l.val*4)<2147483647 ∧ err=.Parse

/-- NIY_scan_native.rs.txt SHA256 OPENHASH, descriptor-only split after K051.
"assert_eq!(compact::OFF_OPENINGS,10055);assert_eq!(q.len(),832);"
"assert_eq!(observed,proof[start..start+832].as_ptr() as usize);".
Byte values are supplied by the separately CLOSED getter packet on its domain. -/
def openingCut (offset length expectedAddress returnedAddress : Nat) : Prop :=
 offset=10055 ∧ length=832 ∧ returnedAddress=expectedAddress

theorem step_ok (first rest : Reply) (run : step first rest=.Ok ()) :
 first=.Ok () ∧ rest=.Ok () := by
 cases first with
 | Err err => cases run
 | Ok unit => cases unit;exact ⟨rfl,run⟩

/-- This conditional algebraic fact consumes the SAME replies/tail; it supplies
no native full-function association, and does not assume that the tail succeeds. -/
theorem prefix_ok (reply : Fin 4 → Reply) (tail : Reply)
 (run : chain reply tail=.Ok ()) :
 reply ⟨0,by decide⟩=.Ok () ∧ reply ⟨1,by decide⟩=.Ok () ∧
 reply ⟨2,by decide⟩=.Ok () ∧ reply ⟨3,by decide⟩=.Ok () ∧ tail=.Ok () := by
 unfold chain at run
 obtain ⟨h0,rest⟩ := step_ok _ _ run
 obtain ⟨h1,rest⟩ := step_ok _ _ rest
 obtain ⟨h2,rest⟩ := step_ok _ _ rest
 obtain ⟨h3,tail⟩ := step_ok _ _ rest
 exact ⟨h0,h1,h2,h3,tail⟩

#print axioms prefixCut
#print axioms m31Cut
#print axioms openingCut
#print axioms step_ok
#print axioms prefix_ok
end NIY_ScanCuts
'''.replace('PREFIXHASH',a).replace('OPENHASH',b)
# Parenthesize the descriptor projection independently of the conjunction.
s=s.replace('received i |>.address = expected i','(received i).address=expected i')
(E/'NIY_ScanCuts.lean').write_text(s)
print('Authored scan prefix/M31/descriptor cut definitions and same-reply prefix algebra; full native scan association explicitly remains open.')
