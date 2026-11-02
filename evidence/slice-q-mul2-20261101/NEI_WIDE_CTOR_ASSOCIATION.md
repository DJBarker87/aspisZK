The actual frozen WideExact::from_limbs rejects iff any of its eight raw U32
coordinates is >= P; otherwise it returns exactly the nested CM31/QM31/WideExact
record in source order. Domain is all raw U32 input words, including rejection.
The function is pure, with no mutable receiver or runtime side effect. Its
Some and M31 occurrences are typed transparent record/enum constructors, not
opaque callees. No canonical-input premise is silently added.

E008 extracts the reached ACTUAL frozen method with all field declarations
visible; no FunsExternal/TypesExternal holes. Its minimal safe wrapper simply
calls that method; wrapper and actual source hashes are recorded. The nominal
carrier map copies the eight fields in order; same_result compares all Result
branches after this map. The coherent model's constructor/observation law is
NEI_WideCtorLaw.limbs_result/complete. No NEG law is reproved.

K031 calls the actual frozen E::from_limbs and observes the complete Option tag
and all eight result fields through its exact to_limbs projection. On all raw
U32[8] inputs it compares against the same guard plus the unchanged array.
K032 corrupts one valid result coordinate and substitutes Some for rejection;
it fails the intended assertion. Exact KMX patch and strict pair audit cover the
array copies; graph/lock and all frozen source bytes remain unchanged. There
is no multiplication, Option<fn>, observer, mutable static, or native contract.

This reclassifies only P6/D188 native semantic transport under owner option A;
it removes no tool trust. Old NEB credits remain suspended, and none is used.
All caller edges into this function remain separately necessary.
