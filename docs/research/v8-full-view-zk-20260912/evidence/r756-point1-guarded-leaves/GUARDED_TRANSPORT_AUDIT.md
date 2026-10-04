# R753 point-1 guarded transport leaf audit

Generator SHA256: `ad6e5218d7a93f04ae57a2c34e075b9bec2dd757c8bf6494f189d801e20f4846`
Plan SHA256: `55f19bf194589ef1229ae6d96ce0d7ef16b1b8d3466b40d00cc0e9fa4b906dd4`
Generated manifest SHA256: `d5006d4d6570a81103d1d972e965161f85c1884347cb7c0f1d6ca307357d86ef`

The generator check passed with 323 planned guarded leaves, 20 existing R748 `w_i` leaves skipped, and 303 new unique leaves. The leaves were split into 10 chunks of at most 32.

Each new leaf reuses the proved R754 transport theorem. It states only the fixed selected point-1 transport value under its source-bit guard and the literal inactive-table branch. It does not prove the transpose/chord/gather assembly or a joint privacy theorem.

## Per-chunk results

| Chunk | Target | Leaves | Exit | Wall | Peak RSS KiB | Swap | Source SHA256 | Receipt SHA256 | Log SHA256 |
|---|---|---:|---:|---:|---:|---:|---|---|---|
| Point1GuardedChunk00.lean | `AspisV8R19/Point1GuardedChunk00.lean` | 32 | 0 | 0:02.53 | 3317768 | 0 | `498df6f2fbfeeff474487225797499e9a48d6c466dd094a46b5e688af743555c` | `773aa855a182671597a682eb7a26c9bf16a6cb3fb5b17922890eba68efae5656` | `ee7cb2f6283e19b194d6436fa77f0d62566b10b87611ce30630df42013a5fa91` |
| Point1GuardedChunk01.lean | `AspisV8R19/Point1GuardedChunk01.lean` | 32 | 0 | 0:02.50 | 3317456 | 0 | `d477bca5ad3b338c279f6db8f5ef2c7e4a75fd315491b8dd1b45cbb134ff653f` | `53585bf5a827e18d4e54264c12ae128eed24cdd0754ca5bcdab89fb521fa1ea3` | `8f20567a869419318e404155e1a77df92f2dcad92ba9295c35e00ca4b58b17e8` |
| Point1GuardedChunk02.lean | `AspisV8R19/Point1GuardedChunk02.lean` | 32 | 0 | 0:02.55 | 3317172 | 0 | `d6777e671431fdf1154ab7608c8551750878a4065f0cbfb1cdc487178eb8c23c` | `109c19ae0fc2a37a3c8353438e9b52c8a407f1c6ae7e89a52a51ec12b3945de0` | `5f9f52ea41ea72942a1a8442fe20f3d14966d55c6885f5717939033447b31cb0` |
| Point1GuardedChunk03.lean | `AspisV8R19/Point1GuardedChunk03.lean` | 32 | 0 | 0:02.57 | 3316244 | 0 | `b2d0fe33974f47b14ee6299fa75cb212204337113e6d142c77285a3be29749ed` | `e1c53a3811f22689ef82892380a7dc05b98a273dd7c491035ddccbc9d8f3445a` | `949badfd6948e5b115faa3cbd55e3d2c3a952677ccb1e0e8d8769ed8d1e72192` |
| Point1GuardedChunk04.lean | `AspisV8R19/Point1GuardedChunk04.lean` | 32 | 0 | 0:02.58 | 3317356 | 0 | `1109b02b3227f58f86c411726d00582b8f655d38d4cd1fd072ccf5fee4a0d426` | `8f1640252cdd6eb9b8bf8c25f0da334845372d70ba7ce9e0ee9aab8ab9ffb0f5` | `3fa91ef2c2731a2a461e493b0bb558e17ce4aaffaa4dbceecd9a941f59a07370` |
| Point1GuardedChunk05.lean | `AspisV8R19/Point1GuardedChunk05.lean` | 32 | 0 | 0:02.59 | 3317300 | 0 | `268f0cd6538a14b93271a474cefee0d93c97693c2077cca0edce1051f51df7ff` | `92506ffc12d0ac664f463059ae640e76dfd4e35db795f0019bca3b9fedf3310a` | `256cba4b36b4b491882255832830fdf6a4f21be4eba5d4ac271ca64fbf9f1134` |
| Point1GuardedChunk06.lean | `AspisV8R19/Point1GuardedChunk06.lean` | 32 | 0 | 0:02.54 | 3317092 | 0 | `375cfea78bffc8a52723bb88a24925b8348c87f474a4b4f1f218ab726faecf6a` | `48a0b0fa14b19327d6efc1b57ffd785920a8eaadee18ade01f8422f7fa0c0350` | `a9a4a6a9dd7740d1274e032d41d1bb1db9406884c5ef4b95fe263407638032ee` |
| Point1GuardedChunk07.lean | `AspisV8R19/Point1GuardedChunk07.lean` | 32 | 0 | 0:02.51 | 3316864 | 0 | `bc2e9252c87c0e0d62f9f6efc4744922ad433f94e839ad9d8ffa8c20566c65b1` | `c7616168f2d3413314c68cb95d140b3720b5f2df79ceb4ed457ed14c1b70c775` | `0511f09ad71872990b3be5e5f227c1fbf7bc485dee7a1e787bc9a7d90fb4245f` |
| Point1GuardedChunk08.lean | `AspisV8R19/Point1GuardedChunk08.lean` | 32 | 0 | 0:02.59 | 3316540 | 0 | `4c8f23ed3a09472a36d010a1707b67b6417ea11c01d884f4515459ca901cc5a2` | `e6f7957eea66a797dc0e6a77657112038ee3b34ecd9ed35c81250d8b2de1bc8d` | `9ab06fbdc6d0d741ae79d1f458c99c632c771e2ee0e797176c15a54c38fb6a35` |
| Point1GuardedChunk09.lean | `AspisV8R19/Point1GuardedChunk09.lean` | 15 | 0 | 0:01.84 | 3306784 | 0 | `cd00068040219a6385a7078c5190d540da048c1ba3d0cea7c151b10acfbc35ac` | `e5b6beb38498913bf0dcb0f1f88e2342287b40720ed9bdeff1d47251a63f38e2` | `1c532b42ed11dbc2c864ba1e5f32e0797396be081bbc450df76c86469d639bb0` |

## Axiom audit

All 303 generated leaf declarations have explicit `#print axioms` output. Every declaration reports `[propext, Classical.choice, Quot.sound]`; no `sorryAx` appears.

## Exact generated leaf indices

```text
4,64,65,66,80,81,82,88,89,90,92,93,94,95,128,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,163,164,165,166,167,168,169,170,171,172,173,174,175,176,179,180,181,182,183,184,187,192,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,384,385,386,448,449,450,512,513,514,576,577,578,640,641,642,704,768,832,896,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991
```

## Preserved failed attempt

The initial chunk-00 attempt was preserved separately: target `AspisV8R19/Point1GuardedChunk00.lean`, failed source SHA `313b74a44ef7e65a09205a33e314228424c90e8cf552972bb544ca5499ba2f07`, exit 1, wall 0:02.52, peak RSS 3307240 KiB, swap 0; receipt `.r21-scratch/aspis-focus-1791144418977612000.receipt.json` (SHA `e9e8127dbe371f9f13f881f69647a1b977ee9da50bbd90099d291d3ab6f817e7`), log `.r21-scratch/aspis-focus-1791144418977612000.log` (SHA `cdf4a46b4d52ad5bb59a232728db029ce078b1d56120cc1f8e4f2c3248645bcb`). It predates the approved generator fixes and is not relied on.

## Boundaries

No remaining chunks beyond these 303 were compiled. The separate 196 nonzero point-basis leaves, full finite gather schedule, transpose/chord assembly, selected-column relation, universal joint privacy proof, and source execution correspondence remain outside this result.
