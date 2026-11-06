# Retired lane shapes and precise replacement

K064 (native iteration) and K067 (constructor control) are retained TIMEOUTs.
Neither is resubmitted. No larger cap or timeout is used.

K064 replacement separates four native statements over an arbitrary pre-state:
(1) exact source digest32 slice at48+32*level, one call, reply/error relay;
(2) one arbitrary selected word written iff decoding succeeds;
(3) one arbitrary other level/word unchanged, including rejecting return;
(4) guard tag after write, reducing node equality with arbitrary-word windows.
Each needs its own matching corruption control under the identical KMX patch.
NKF_LaneFactor proves the symbolic geometry and reconstruction; NKF_LaneTrace
supplies existing frame/induction; NKF_LanePrefix proves chronological prefix,
log bound and successful exhaustion. These lemmas do not certify native cuts.

K067 replacement separates scalar/header/master, root word, frontier row/word
and untouched-allocation frame. The negative control must corrupt precisely the
selected returned field BEFORE computing good. NKF_LaneConstructor reconstructs
the canonical AdapterRw lane/tree types from arbitrary row/word observations,
without reducing20×8cells or the empty-root table. Native control OPEN.

The final Kani invocation was reserved for K081, as instructed. Its owned temp
path compilation failure exhausted that allowance. These new Lean shapes
therefore remain ready for future native cuts, with zero native credit.
