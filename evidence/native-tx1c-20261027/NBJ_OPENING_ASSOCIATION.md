# Opening address and physical read source cuts

Source: frozen candidate.rs:29-31. The body has only scalar arithmetic and
immutable range construction; it reads no proof byte and writes no state.
The harness observer reads exactly one selected byte. The full source body
is invoked by the positional window harnesses; no source helper replaces it.

K001 checks all i<22 scalar start/end and fit on the57607-byte proof. K003
checks arbitrary832-byte slice content, pointer and length. K002's full
symbolic-address observation timed out; K010's fixed-opening832-byte observer
also timed out. Both excluded. K011 onward split that physical observer into
26 fixed32-byte windows, with arbitrary selected coordinate/reply byte, and
otherwise zero surroundings. The zero surroundings are a HARNESS class, not
a new caller precondition. No arbitrary-byte global native execution is
claimed solely from these harnesses.

NBJ_Address.opening_range is the exact installed range operation for all
proof bytes and lengths, not merely an accepted opening. NBJ_WindowCover
provides symbolic relocation/coverage for arbitrary memory images. These
laws explain the positional split. A full direct bridge additionally needs
audited source-cut locality tying the immutable native range carrier to that
same memory image. The reports must retain that obligation if it is not
instantiated; equal bytes on zero surroundings alone cannot discharge it.

NBI_Views.opening_leaf remains the existing checked SAME-proof/SAME-index
model composition; NBJ_Opening.selected_leaf imports it read-only. No generic
model theorem is called a complete native leaf traversal or batch bridge.
