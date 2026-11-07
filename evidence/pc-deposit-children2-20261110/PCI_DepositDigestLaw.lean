import PCI_DepositWordWindow
import PCI_ArrayCanonical
import PCI_IteTransport
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositDigestLaw

theorem flip {T : Type} (x : U32) (yes no : T) :
    (if x>=2147483647#u32 then yes else no)=(if x<2147483647#u32 then no else yes) := by
 have h : (x>=2147483647#u32) ↔ ¬(x<2147483647#u32) := Nat.not_lt.symm
 simp only [h,ite_not]

theorem value (h : Array U8 80#usize) (base : Nat) (bound : base+32≤80) :
    AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical (PCI_DepositWordWindow.cut h base bound)=
      ok (if PCI_ArrayCanonical.model (PCI_DepositWords.model h base) then
        .Ok (PCI_DepositWords.model h base) else
        .Err AspisR1TerminalDecoder.atomic_statement.AtomicStatementError.NonCanonicalDigest) := by
 rw [NFY_NBP_DigestDecode.result]
 unfold NFY_NBP_DigestDecode.decoded
 simp only [NFY_NBP_DecodeWord.word,NFY_NBP_DecodeWord.P,PCI_DepositWordWindow.limbs]
 rw [PCI_DepositWordWindow.word h base 0 bound (by omega),PCI_DepositWordWindow.word h base 1 bound (by omega),PCI_DepositWordWindow.word h base 2 bound (by omega),PCI_DepositWordWindow.word h base 3 bound (by omega),PCI_DepositWordWindow.word h base 4 bound (by omega),PCI_DepositWordWindow.word h base 5 bound (by omega),PCI_DepositWordWindow.word h base 6 bound (by omega),PCI_DepositWordWindow.word h base 7 bound (by omega)]
 unfold PCI_ArrayCanonical.model PCI_DepositWords.model
 simp only [Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ]
 simp only [flip,PCI_IteTransport.nested,PCI_IteTransport.decided]
 rfl

#print axioms flip
#print axioms value
end PCI_DepositDigestLaw
