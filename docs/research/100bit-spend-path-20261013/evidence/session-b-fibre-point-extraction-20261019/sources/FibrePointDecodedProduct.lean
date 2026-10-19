import FibrePointSuccessOutput

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace R17FibrePointDecodedProduct
open AspisR1QueryGeometryActual

abbrev P := 2147483647

def decodeM31 (x : Std.U32) : ZMod P := x.val

def decodeCM31 (x : field.CM31) : ZMod P × ZMod P :=
  (decodeM31 x.a, decodeM31 x.b)

def decodeEntry (x : Std.U32 × Std.U32) : ZMod P × ZMod P :=
  (decodeM31 x.1, decodeM31 x.2)

def decodePoint (x : domain.Point field.M31) : ZMod P × ZMod P :=
  (decodeM31 x.x, decodeM31 x.y)

def cm31Product (x y : ZMod P × ZMod P) : ZMod P × ZMod P :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- Exact arithmetic obligations for the opaque CM31 constructors retained by
Charon. The extracted fibre_point body itself is in the imported owner. -/
structure CM31OpsSemantics (ops : CM31Ops) : Prop where
  new_spec : ∀ (a b : field.M31) (c : field.CM31), ops.new a b = .ok c →
    decodeCM31 c = (decodeM31 a, decodeM31 b)
  mul_spec : ∀ (a b c : field.CM31), ops.mul a b = .ok c →
    decodeCM31 c = cm31Product (decodeCM31 a) (decodeCM31 b)

/-- Source-body success plus explicit CM31 arithmetic laws gives the exact
complex-coordinate product output. The remaining table-factor/stored-domain
identity is intentionally a separate source correspondence. -/
theorem successful_fibre_point_decodes_to_product
    (ops : CM31Ops) (hspec : CM31OpsSemantics ops)
    (u : domain.FibreIndex)
    (ix iA iB : Std.Usize)
    (entryA entryB : Std.U32 × Std.U32)
    (left right product : field.CM31)
    (hget : domain.FibreIndex.get u = .ok ix)
    (hmask : lift (ix &&& 511#usize) = .ok iA)
    (hlookupA : Array.index_usize fast_domain.TABLE_A iA = .ok entryA)
    (hleft : fast_domain.table_value ops entryA = .ok left)
    (hshift : ix >>> 9#i32 = .ok iB)
    (hlookupB : Array.index_usize fast_domain.TABLE_B iB = .ok entryB)
    (hright : fast_domain.table_value ops entryB = .ok right)
    (hmul : ops.mul left right = .ok product) :
    fast_domain.fibre_point ops u = .ok
      ({ x := product.a, y := product.b } : domain.Point field.M31) ∧
    decodePoint ({ x := product.a, y := product.b } : domain.Point field.M31) =
      cm31Product (decodeEntry entryA) (decodeEntry entryB) := by
  constructor
  · exact R17FibrePointSuccessOutput.fibre_point_success_output ops u ix iA iB
      entryA entryB left right product hget hmask hlookupA hleft hshift
      hlookupB hright hmul
  · have hleftDecode : decodeCM31 left = decodeEntry entryA := by
      cases entryA with
      | mk a b =>
        have hnew : ops.new a b = .ok left := by
          simpa [fast_domain.table_value] using hleft
        simpa [decodeEntry] using hspec.new_spec a b left hnew
    have hrightDecode : decodeCM31 right = decodeEntry entryB := by
      cases entryB with
      | mk a b =>
        have hnew : ops.new a b = .ok right := by
          simpa [fast_domain.table_value] using hright
        simpa [decodeEntry] using hspec.new_spec a b right hnew
    have hmulDecode := hspec.mul_spec left right product hmul
    rw [hleftDecode, hrightDecode] at hmulDecode
    simpa [decodePoint, decodeCM31] using hmulDecode

#print axioms successful_fibre_point_decodes_to_product
