# Reservation stall review

09:46UTC review: last compiled target FixtureHashCell4(40998) took4.38s, peak4195332096bytes, swap0. More than ten minutes without a new compiled target is due to aggregate reservation refusals, not an active/pathological Lean reduction. Read-only systemctl inventory finds no running pv12/runjoin scope. Memory cap6G/8G/swap0 is unchanged; no lower fictional reservation or uncapped alternate path is used.

Round5_0 was refused before launch as40999,41000,41001,41002. Four consecutive uncharged refusals for this target; retry limit10 has not been reached.41002 refusal09:44:14.994251UTC reports bounded_reserved59995324416 and projected68585259008 > safe59055800320. Next41003 no earlier than09:47:14.994251UTC. Common rules and restored flag re-read;09:20 flag update extends global accepted ranges but does not change this job's assigned40900–41199 range. No foreign scope is modified or stopped.
