import PV_LIB_SPEC_NativeModel
set_option autoImplicit false
namespace PV_LIB_SPEC_NativeKinds
open PV_STX2_Syntax
def atomicBool : Data := .object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 57))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Literal", (.atom "Bool"))]), (.object [("Adt", (.object [("id", (.object [("Adt", (.number 81))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Literal", (.object [("UInt", (.atom "U8"))]))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]
def unsafeCell : Data := .object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 116))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("TypeVar", (.object [("Free", (.number 0))]))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]
def maybeDangling : Data := .object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 131))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("TypeVar", (.object [("Free", (.number 0))]))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]
def boolCell : Data := .object [("Adt", (.array [(.object [("id", (.object [("Adt", (.number 116))])), ("generics", (.object [("regions", (.array [])), ("types", (.array [(.object [("Literal", (.atom "Bool"))])])), ("const_generics", (.array [])), ("trait_refs", (.array []))]))]), (.null), (.null)]))]
#print axioms atomicBool
#print axioms unsafeCell
#print axioms maybeDangling
#print axioms boolCell
end PV_LIB_SPEC_NativeKinds
