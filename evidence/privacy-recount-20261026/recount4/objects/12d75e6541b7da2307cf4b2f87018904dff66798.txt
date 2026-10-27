# Fixture coverage of the corrected Kani harness

No gate result is credited until a successful terminal receipt exists.

`pv_runjoin12::inputs` fixes input value 1000; nullifier key digest(10), salt digest(100); selected_second=false; membership index 0x54321 and siblings digest(2000+20*l); super siblings digest(3000), digest(3100), digest(3200), directions true,false,true. It fixes second occupancy 1 and second commitment digest(900). The first commitment and second occupancy inverse are arbitrary raw M31 words, so this family includes the actual computed note commitment and inverse of sentinel 1020 without assuming a hash result.

Transfer fixes out=600, recipient owner/salt digest(300)/digest(400), recipient value600, change owner/salt digest(500)/digest(600), change value400. Withdrawal fixes out=250, recipient=None, change owner/salt digest(700)/digest(800), value750. Every invocation fixes asset77. All source digest seeds plus their seven lane offsets are below P, so the omitted modulo in the harness seed constructor does not change these fixture constants.

Snapshot pool[1;32], domain[5;32], sequence0 and next_pair_index0 are fixed. Current root and frontier words are arbitrary, including the exact r0_fixture snapshot; no source helper return is assumed or stubbed. Both complete actual mapper functions execute; the reference wrapper supplies its own actual pair_empty_roots computation to the extracted owned reference body.

`part=1` checks the thirteen nonpath witness fields. `part=2` checks both complete path arrays. `part=3` checks all five public fields. The union covers all fields; it is only a composition plan until the corresponding actual checks pass. The all-field transfer run with the older inverse restriction timed out and establishes no fixture coverage.
