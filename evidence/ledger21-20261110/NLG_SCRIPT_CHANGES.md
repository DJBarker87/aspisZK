# Own script adaptations

NKW scripts reused with NLG path/prefix and ledger20 predecessor pins; 30 disjoint raw groups retained. Own wrappers only; shared launcher/reservation/walker untouched. All validation predicates unchanged or strengthened. NKU/NKY added to selected roots/imports/objects. No compile repetition or cache replacement. Close scope pins and compares every predecessor object before exporting NLG objects.

Source-review preflight initially expected a nongeneric signature; replaced with generic-aware function match. Failed before any source conclusion; same body hash checks retained.

Retained-input reader initially decoded an archive whose receipt pins archive bytes. Corrected to test the receipt hash against archive bytes first, otherwise decoded bytes. Neither input nor expected hash changes.
