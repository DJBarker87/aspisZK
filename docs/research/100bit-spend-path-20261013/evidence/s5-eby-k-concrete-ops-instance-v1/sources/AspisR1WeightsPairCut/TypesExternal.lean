import Aeneas

namespace core.iter.adapters.filter
/-- Explicit type placeholder for the std Filter model at this extraction cut. -/
structure Filter (I P : Type) where
  iterator : I
  predicate : P
end core.iter.adapters.filter
