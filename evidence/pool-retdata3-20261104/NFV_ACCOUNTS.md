# Account association under ruling (af)

Preparation; no new native credit yet. Frozen revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
The original NFO_read::association names are retained. Exact KMX patch:
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
AccountMeta layout: Pubkey [u8;32], two bool fields, byte alignment: 34 bytes.
Six entries copy 6*34=204 bytes; loop bound 204+1=205.
No NFR passing or timed-out configuration will be repeated unchanged.
