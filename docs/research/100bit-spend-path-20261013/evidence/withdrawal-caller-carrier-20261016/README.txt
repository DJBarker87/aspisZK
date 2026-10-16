ASWP caller-to-retained-validator carrier, Lean4.32

ExtractedWithdrawalCallerCarrier copies all9 public fields in both directions,
proves the roundtrips, maps all14 errors, and proves equality of the actual
common and complete validation results, including failure/divergence. It then
uses actual ASWP encoder success to obtain the existing HelperValidated on the
fixed serializer carrier, hence0<amount<2^30. It assumes no helper success and
asserts no terminal/verifier/ASF8 reachability or omitted-metadata binding.

The original joint import fails because two generated Types declare the same
global Error discriminant instance. The isolated Caller Types adapter follows
A's36dd8dc0a method: expand only that attribute to its identical read_discriminant
and a fully qualified instance. Original mirrors/cache remain unchanged. The
generator is pinned here; inverse transformation recovers every original byte.
All14 constructor codes check under both originals and adapter; printed
read_discriminant/audit logs are byte-identical SHA675df86099a71458bdc3ded0f34e30207b3abfd2a5f889bf9d8d03540f0c0c2b.

Adapted Types/Funs, unchanged standalone E→V proof and constructor audit passed.
The final carrier check passed1.610s, sampled cgroup623,833,088B, swap0; all8
requested exports use only propext/Classical.choice/Quot.sound. Each job used
6GiB high/8GiB max/swap0 and reused all checked predecessors. The two failed
carrier attempts (syntax, then field-copy rewrite normalization) and original
joint-import failure are retained. The final manifest corrects initial shorthand
canonical-path labels; staged source/object/runtime hashes did not change.

The97-member archive includes source snapshots, all runs, exact external
closures/import journals, final receipts and runner. Objects are retained at
host aspis-r1-j1a-caller-adapted-20261016/objects; no original object overwritten.
