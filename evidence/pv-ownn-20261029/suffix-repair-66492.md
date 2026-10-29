66492 compiled scanner_suffix_length and scanner_decoded_cast with standard
axioms, but failed at the subsequent simpa between local w/t aliases and
width/trailing. The replacement explicitly changes hd to the dependent
Fin.cast htlen type before eliminating List.get, and simplifies the optional
lookup in the goal separately. No dependent suffix-length rewrite is used.
The entire failed66492 scalar/restore result receives no credit; replacement
source SHA is changed before66493. No cap or Link definition changes.
