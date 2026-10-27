# Recorded op223 whole-prover cost (reused, no new timing)

Exact receipt: `evidence/pv-quiet-20261027/comparison.json`, measurement scope receipt `evidence/pv-quiet-20261027/measurement-scope/receipt/receipt.json`, summarized in that packet’s README (D286 gate, lead D289 acceptance). Shipped control `c57a344726745387efb38d1571d885c69ce829ee`; op223 candidate `8873306db187ec0b530d2469d4ec0f7f85e25365`. Five fresh matched processes per side, coins100–104.

|Fixture|Control median s|Candidate median s|Candidate/control|Measured median delta s|
|---|---:|---:|---:|---:|
|transfer|14.384269323|14.377724028|0.9995449685449413|−0.006545295|
|withdrawal|14.239355475|14.248478673|1.0006407030160893|+0.009123198|

The cumulative projection adds these recorded median differences to batch1/2/3 per-call projections, then divides by14.38s for the requested percentage. Mixed measurement/input conditions make this a finite projection; it does not establish merged-candidate timing, universal cost or a formal bound. The new quiet-window gate remains unrun.
