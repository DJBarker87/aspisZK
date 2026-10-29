import PV_2TNV_PublicWindows
set_option autoImplicit false
namespace R1Z.PV_RJ4IDB_ByteWindow
open Aeneas Aeneas.Std AspisR1.PV_2TNV_PublicEncoding
/-- Project a bounded inner word from two equal native byte windows. -/
theorem word_window (l r : List U8) (a b width off : Nat)
 (h : (l.drop a).take width = (r.drop b).take width)
 (bound : off+4≤width) : word l (a+off) = word r (b+off) := by
 unfold word
 have same := congrArg (fun xs : List U8 => (xs.drop off).take 4) h
 rw [AspisR1.PV_2TNV_PublicWindows.nested _ _ _ _ _ bound,
 AspisR1.PV_2TNV_PublicWindows.nested _ _ _ _ _ bound] at same
 exact congrArg AspisR1.PV_2TNV_ByteEncoding.littleEndian same

theorem digest_window (l r : List U8) (a b width off : Nat)
 (h : (l.drop a).take width = (r.drop b).take width)
 (bound : off+32≤width) : digest l (a+off) = digest r (b+off) := by
 funext i
 unfold digest
 rw [Nat.add_assoc,Nat.add_assoc]
 exact word_window l r a b width (off+4*i.val) h (by have hi := i.isLt; omega)
#print axioms word_window
#print axioms digest_window
end R1Z.PV_RJ4IDB_ByteWindow
