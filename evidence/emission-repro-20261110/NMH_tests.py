#!/usr/bin/env python3
"""Small parser/comparator controls, not formal proof or native credit."""
import sys
sys.dont_write_bytecode=True
from NMH_names import declarations
from NMH_compare import definitions,nhr_types
s='''namespace A
/- namespace Wrong /- nested -/ -/
section
namespace B
/-- [crate::foo] Source: 'x.rs', lines 1:0-1:1 -/
def foo : Nat := 1
end B
end
namespace C
def foo : Nat := 2
end C
end A
'''
assert [d['name'] for d in declarations(s)]==['A.B.foo','A.C.foo']
assert declarations('-- namespace Wrong\nnamespace X\ndef x := "namespace Wrong"\nend X')[0]['name']=='X.x'
assert definitions('def f := 1\ndef g := 2')['f']['sha256']!=definitions('def f := 2\ndef g := 2')['f']['sha256']
assert nhr_types('@[discriminant isize]\ninductive X where\n| a')=='inductive X where\n| a'
assert nhr_types('namespace A\ndef f := 1\nend A')!=nhr_types('namespace B\ndef f := 1\nend B')
assert nhr_types('def f := 1')!=nhr_types('def f := 2')
print('six parser/comparator controls passed; namespace/body changes remain unequal')
