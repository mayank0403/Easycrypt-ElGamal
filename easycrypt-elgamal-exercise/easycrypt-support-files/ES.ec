clone import BitWord as Bits with
  op n <- k
proof gt0_n by exact/gt0_k
rename
  "word" as "bits"
  "dunifin" as "dbits".
import DWord.

type hkey.

op dhkey: { hkey distr | is_lossless dhkey } as dhkey_ll.
hint exact random : dhkey_ll.

op cdhkey : { int | 0 <= cdhkey} as ge0_cdhkey.
schema cost_dhkey `{P} : cost[P: dhkey] = N cdhkey.
hint simplify cost_dhkey.

op hash : hkey -> group -> bits.
op chash : {int | 0 <= chash } as ge0_chash.
schema cost_hash `{P} {k : hkey, g : group} : cost [P:hash k g] = cost [P: k] + cost[P:g] + N chash.
hint simplify  cost_hash.

module type AdvES = {
  proc guess(_: hkey * bits) : bool
}.

module ES0 (A : AdvES) = {
  proc main () : bool = {
    var b, hk, h;
    hk <$ dhkey;
    h  <$ dbits;
    b  <@ A.guess(hk, h);
    return b;
  }
}.

module ES1 (A : AdvES) = {
  proc main () : bool = {
    var b, hk, z;
    hk <$ dhkey;
    z  <$ dt;
    b  <@ A.guess(hk, hash hk (g ^ z));
    return b;
  }
}.
