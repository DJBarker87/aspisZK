# Actual CM31 multiplication maps

The wrapping theorem maps the actual emitted CM31 multiplication call to the R22 `wrappingCMMul` expression for all inputs. The checked-current theorem then requires canonicality of both CM inputs and equates that same mapped call with the extracted checked CM31 multiplication. The wrapping theorem separately derives canonicality of the wrapped output for canonical inputs via the retained R22 theorem. These are Lean source/model results; no compiler binary or runtime refinement is asserted.

The earlier failed attempts are preserved in `/tmp/root-s9-actual-cm-result-v1-20261022/evidence/lean.log` and `...-v2-20261022/evidence/lean.log`; v3 is the accepted immutable source used here.
