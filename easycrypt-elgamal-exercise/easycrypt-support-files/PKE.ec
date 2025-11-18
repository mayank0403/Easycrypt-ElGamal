require import DBool.

theory PKE.

  type pk_t.
  type sk_t.
  type pt_t.
  type ct_t.

  module type Scheme = {
    proc key_gen() : pk_t * sk_t
    proc encrypt(pk : pk_t, m : pt_t) : ct_t
    proc decrypt(sk : sk_t, ct : ct_t) : pt_t
  }.

  module Correct (S : Scheme) = {
    proc main(m : pt_t) : bool = {
      var pk, sk, ct, m';

      (pk, sk) <@ S.key_gen();
      ct <@ S.encrypt(pk, m);
      m' <@ S.decrypt(sk, ct);

      return (m = m');
    }
  }.

  module type INDCPA_Adv = {
    proc gen_query(pk : pk_t) : pt_t * pt_t
    proc guess(ct : ct_t) : bool
  }.

  module INDCPA (S : Scheme) (A : INDCPA_Adv) = {
    proc main() : bool = {
      var pk, sk, m0, m1, b, b', ct;

      (pk, sk) <@ S.key_gen();
      (m0, m1) <@ A.gen_query(pk);
      b <$ {0,1};
      ct <@ S.encrypt(pk, if b then m1 else m0);
      b' <@ A.guess(ct);

      return (b = b');
    }
  }.

end PKE.
