require import CyclicGroup.

module type Adversary = {
  proc guess(gx gy gz : group) : bool
}.

module DDH0 (A : Adversary) = {
  proc main() : bool = {
    var b, x, y;

    x <$ FDistr.dt;
    y <$ FDistr.dt;
    b <@ A.guess(g ^ x, g ^ y, g ^ (x * y));
    return b;
  }
}.

module DDH1 (A : Adversary) = {
  proc main() : bool = {
    var b, x, y, z;

    x <$ FDistr.dt;
    y <$ FDistr.dt;
    z <$ FDistr.dt;
    b <@ A.guess(g ^ x, g ^ y, g ^ z);
    return b;
  }
}.
