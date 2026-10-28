# Next query split (unrun)

K063/K064 timed out for i=1..15 because the prefix constructor pushes a variable number of bytes. Keep the original pointer/capacity/value contract but initialize `Vec::from(initial)` with `initial:[u8;128]`, then `truncate(64+4*i)`, for1<=i<16. Check the arbitrary live prefix, len/cap128, append the four source bytes with the exact KMX helper, and check the final length/cap128 plus prefix/appended window. Run the same configuration with XOR1 in the asserted byte as negative control.

This constructs every possible live prefix in an actual owned capacity128 Vec; initialized spare bytes are never observed because this case does not reallocate. The next case i=16 has len=cap128, so no uninitialized spare remains at that boundary. Existing controlled K059/K060 establish the same array-to-owned-Vec constructor at1736 bytes, but do not count as verification of this new128-byte transition.

An analogous256-byte constructor/truncate split is available for i=17..21 if K067/K068 do not complete. Those runs were already submitted before the queue pause; they are retained and never resubmitted. The revised constructor is a new draft, not credited evidence and not a replacement copy stub.
