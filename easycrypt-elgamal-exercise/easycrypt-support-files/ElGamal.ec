require import AllCore DBool PKE Real.

require import CyclicGroup.

theory ElGamal.

  clone import PKE with
    type pk_t = group,
    type sk_t = t,
    type pt_t = group,
    type ct_t = group * group.

  module ElGamal : Scheme = {
    proc key_gen() : pk_t * sk_t = {
      var pk, sk;

      sk <$ FDistr.dt;
      pk <- g ^ sk;

      return (pk, sk);
    }

    proc encrypt(pk : pk_t, m : pt_t) : ct_t = {
      var y, bet, delt, zet;

      y <$ FDistr.dt;
      bet <- g ^ y;
      delt <- pk ^ y;
      zet <- delt * m;

      return (bet, zet);
    }

    proc decrypt(sk : sk_t, ct : ct_t) : pt_t = {
      var m, bet, zet;

      (bet, zet) <- ct;
      m <- zet / (bet ^ sk);

      return (m);
    }
  }.

  lemma elgamal_correct : hoare [ Correct(ElGamal).main : true ==> res ].
  proof.
    proc.
    inline*.
    wp.
    rnd.
    wp.
    rnd.
    skip.
    progress.
    rewrite !pow_pow.
    rewrite (F.mulC sk0 y0).
    rewrite mulC.
    rewrite -div_def.
    rewrite !log_pow.
    rewrite log_mul.
    rewrite log_pow.
    rewrite sub_def.
    rewrite -F.addA.
    rewrite F.addfN.
    rewrite F.addf0.
    rewrite gpow_log.
    done.
  qed.

  module Game0 (A : INDCPA_Adv) = INDCPA(ElGamal, A).

  module D (A : INDCPA_Adv) = {
    proc guess(gx gy gz : group) : bool = {
      var m0, m1, b, b';

      (m0, m1) <@ A.gen_query(gx);
      b <$ {0,1};
      b' <@ A.guess(gy, gz * (if b then m1 else m0));

      return (b = b');
    }
  }.

  require import DDH.

  section SemanticSecurity.

    declare module A <: INDCPA_Adv.
    axiom a_gen_query_ll : islossless A.gen_query.
    axiom a_guess_ll : islossless A.guess.

    lemma game0_ddh0_equiv : 
      equiv [ DDH0(D(A)).main ~ Game0(A).main : ={glob A} ==> ={res} ].
    proof.
      proc.
      inline*.
      wp.
      call (_ : true).
      wp.
      swap{2} 8-6.
      wp.
      rnd.
      call (_ : true).
      wp.
      rnd.
      rnd.
      skip.
      progress.
      rewrite pow_pow.
      done.
    qed.

    lemma game0_ddh0_pr &m :
      Pr [ DDH0(D(A)).main() @ &m : res ] = Pr [ Game0(A).main() @ &m : res ].
    proof. by byequiv game0_ddh0_equiv. qed.

    module Game1 = {
      proc main() : bool = {
        var pk, sk, m0, m1, b, b', ct, y, bet, delt, z, zet;

        (pk, sk) <@ ElGamal.key_gen();
        (m0, m1) <@ A.gen_query(pk);
        b <$ {0,1};

        y <$ FDistr.dt;
        bet <- g ^ y;
        delt <- pk ^ y;
        z <$ FDistr.dt;
        zet <- g ^ z;
        ct <- (bet, zet);

        b' <@ A.guess(ct);

        return (b = b');
      }
    }.

    lemma game1_ddh1_equiv : 
      equiv [ DDH1(D(A)).main ~ Game1.main : ={glob A} ==> ={res} ].
    proof.
      proc.
      inline*.
      wp.
      call (_ : true).
      wp.
      swap{1} 6 2.
      swap{1} 3 4.
      wp.
      rnd (fun z, z + log (if b0{1} then m1{1} else m0{1}))
          (fun z, z - log (if b0{1} then m1{1} else m0{1})).
      wp.
      swap{2} 5 1.
      rnd.
      swap{2} 4 1.
      call (_ : true).
      wp.
      rnd.
      wp.
      rnd.
      skip.
      progress.
        rewrite sub_def -addA 
                (addC (- log (if b0L then result_R.`2 else result_R.`1)) _) addfN addf0.
        done.
        rewrite sub_def -addA addfN addf0.
        done.
        rewrite -mul_pow gpow_log.
        done.
    qed.

    lemma game1_ddh1_pr &m :
      Pr [ DDH1(D(A)).main() @ &m : res ] = Pr [ Game1.main() @ &m : res ].
    proof. by byequiv game1_ddh1_equiv. qed.

    lemma game1_pr &m : 
      Pr [ Game1.main() @ &m : res ] = 1%r / 2%r.
    proof.
      byphoare.
      proc.
      swap 3 7.
      rnd (fun b => b = b').
      call (_ : true).
      apply a_guess_ll.
      wp.
      rnd.
      wp.
      rnd.
      call (_ : true).
      apply a_gen_query_ll.
      inline *.
      wp.
      rnd.
      skip.
      progress.
        rewrite dbool1E. 
        done.
        apply FDistr.dt_ll.
        apply FDistr.dt_ll.
        apply FDistr.dt_ll.
        done.
        done.
    qed.

    lemma security &m :
      Pr [ INDCPA(ElGamal, A).main() @ &m : res ] = 
      1%r/2%r + (Pr[ DDH0(D(A)).main() @ &m : res ] - 
                 Pr[ DDH1(D(A)).main() @ &m : res ]).
    proof.
      move : (game1_pr &m).
      move : (game1_ddh1_pr &m).
      move : (game0_ddh0_pr &m).
      progress.
      rewrite H H0 H1.
      rewrite RField.addrC -RField.addrA (RField.addrC (- inv 2%r) _) RField.subrr RField.addr0.
      done.
    qed.

  end section SemanticSecurity.

end ElGamal.

