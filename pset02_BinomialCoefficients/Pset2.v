(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 2 *)

(* Author: Samuel Gruetter <gruetter@mit.edu>

This pset will introduce you to one of the major applications of formal
reasoning about programs: proving that an optimized program behaves the same as
a simple program.

Once again, you can check the tips section near the bottom of this file for some
useful tips and tricks to help you navigate Coq and Ltac. In the signature file there
is a hint specific to the problems in this pset that you can consult if you find
yourself stuck!

Imagine you're writing a program that needs some function F. You know how to
implement F naively, but as you run your program, you notice that it spends a
lot of time in the function F. You find a library which claims to provide a very
efficient implementation of F, but looking at its source code, you don't really
understand why this code should calculate F, and you've seen some bug reports
against previous versions of the library, so you can't really know whether this
library implements F correctly.  Since you care a lot about writing a correct
program, you finally decide to keep using your naive slow implementation.
Formal reasoning about programs to the rescue! If the authors of the library
want to increase the user's trust in their library, they can include the naive
but simple-to-understand version of F in their library as well and write a
proof that for all possible inputs, the optimized version of F returns the same
value as the simple version of F.  If that proof is in a machine-checkable
format (e.g. in a Coq file), the library users do not need to understand the
implementation of the optimized F, nor the body of the proof, but can still use
the optimized F and be sure that it does the same as the simple implementation,
as long as they trust the proof checker.

In this pset, we will put you in the role of the library author who writes a
naive version of F, an optimized implementation of F, and a proof that the two
of them behave the same. *)

Require Import Coq.NArith.NArith. Open Scope N_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Lia.
Require Import Frap.Frap.
Require Import Pset2Sig.

(* As usual, the grading rubric for this pset is in Pset2Sig.v. *)

Module Impl.
  (* Recursive functions *)
  (* ******************* *)

  (* We will need some recursive functions in this PSet. Defining recursive
     functions in Coq can be a bit tricky, because Coq only accepts recursive
     functions that very obviously terminate.

     For natural numbers represented as "nat", and for data structures like the
     abstract syntax trees we saw in class, recursive functions can usually be
     defined using "Fixpoint", because each recursive call is made on a subterm of
     the original argument, which is required for Coq to be convinced that the
     recursive function terminates. Coq accepts the [fact_nat] function below
     because the recursive call [fact_nat n'] operates on [n'], which is a subterm
     of [n].
   *)
  
  Fixpoint fact_nat (n : nat) : nat :=
    match n with
    | O => 1
    | S n' => (n' + 1) * (fact_nat n')
    end.
  
  (*
     In this pset, however, we want to use the binary representation of natural
     numbers, which is called "N" in Coq.  This representation stores numbers as
     lists of binary digits, so recursive functions on these numbers don't
     decrease by one on every call: they remove one binary digit on every call
     (which corresponds to dividing by two).

     So, a Fixpoint on N called with the binary number "1101" can only make
     recursive calls with the number "110".  To make recursive calls with one
     less than the argument, i.e. with 1100 in this example, we need a special
     recursion operator:

       N.recursion base_case update_fn n_iters

    This pattern can only define functions recursing over a natural number until
    it reaches 0, with one recursive case where the recursive call is for one less
    than the argument. It corresponds to the following function on nat: *)

  Fixpoint nat_recursion {A} (base_case: A) (update_fn: nat -> A -> A) n_iters :=
    match n_iters with
    | 0 => base_case
    | S n => update_fn n (nat_recursion base_case update_fn n)
    end%nat.

  (*
    To show how we can use this function, we can define an alternate version of
    fact_nat as follows:
   *)

  Definition fact_nat' : nat -> nat :=
    nat_recursion 1%nat (fun n recurse => (n + 1) * recurse)%nat.


  (* To make definitions more readable, we have defined a notation for
     N.recursion that mirrors the structure of the match statement in the original
     fact_nat fixpoint but actually desugars to a definition like fact_nat'.
     We'll be using the following factorial function, defined using our notation,
     for the rest of this assignment:
   *)

  Definition fact: N -> N :=
    recurse by cases
    | 0 => 1
    | n + 1 => (n + 1) * recurse
    end.

  (* The above function implements factorial, i.e. "fact n = 1 * 2 * ... * n".  In
     the recursive case, you can use the word "recurse" to refer to the result of
     the recursive call. *)

  (* Aside: If you don't like the above notation and want to see the real
     definition, you can do this:

  Close Scope N_recursion_scope.
  Print fact.
  *)

  (* Let's compute the first few values of fact: *)
  Compute fact 0.
  Compute fact 1.
  Compute fact 2.
  Compute fact 3.
  Compute fact 4.

  (* Instead of writing "(fact x)" all the time, it's more convenient to just
     write "x!", so we make a Notation for this: *)
  Local Notation "x !" := (fact x) (at level 12, format "x !").

  (* Exercise: Define a simple exponentiation function in the same style, so that
     "exp base n" equals "base^n". *)

  Definition exp(base: N): N -> N := 
    recurse by cases
    | 0 => 1
    | n + 1 => base * recurse
    end.

  (* Once you define "exp", you can replace "Admitted." below by "Proof. equality. Qed." *)
  Lemma test_exp_2_3: exp 2 3 = 8. Proof. equality. Qed.
  Lemma test_exp_3_2: exp 3 2 = 9. Proof. equality. Qed.
  Lemma test_exp_4_1: exp 4 1 = 4. Proof. equality. Qed.
  Lemma test_exp_5_0: exp 5 0 = 1. Proof. equality. Qed.
  Lemma test_exp_1_3: exp 1 3 = 1. Proof. equality. Qed.

  (* Here's another recursive function defined in the same style to apply a
     function f to a range of values:
     "seq f len start" computes the list [f start; f (start+1); ... f (start+len-1)] *)
  Definition seq(f: N -> N): N -> N -> list N :=
    recurse by cases
    | 0 => fun start => []
    | n + 1 => fun start => f start :: recurse (start + 1)
    end.

  Compute (seq (fun x => x * x) 4 10).

  (* "ith i l" returns the i-th element of the list l.
     To understand the recursion, note that "ith i" returns a function which takes
     a list and, depending on whether i was 0 or not, returns the head of the list
     or the (i-1)-th element of the tail.  If the index is out of bounds, it
     returns the default value 0. *)
  Definition ith: N -> list N -> N :=
    recurse by cases
    | 0 => fun (l: list N) => match l with
                              | h :: t => h
                              | nil => 0
                              end
    | i + 1 => fun (l: list N) => match l with
                                  | h :: t => recurse t
                                  | nil => 0
                                  end
    end.

  (* The standard library already contains a function called "length": *)
  Check length.
  (* However, it returns a "nat", i.e., the representation of natural numbers
     using O and S, which is very inefficient: To represent the number n, it needs
     roughly c*n bytes of RAM, where c is some constant, whereas "N", the binary
     representation of natural numbers, only used c*log(n) bytes of RAM.
     Therefore, we redefine our own length function which returns an N: *)
  Fixpoint len(l: list N): N :=
    match l with
    | [] => 0
    | h :: t => 1 + len t
    end.
  (* Note that since the recursion follows the structure of the data (the list)
     here, we use Fixpoint instead of "recurse by cases". *)

  (* Here's a simple lemma: If we tell "seq" to return a list of length "count",
     it indeed does: *)
  Lemma seq_len: forall f count start, len (seq f count start) = count.
  Proof.
    induct count; simplify.
    - (* base case: count = 0 *)
      equality.
    - (* recursive case: assuming the statement holds for some "count", show that
         it also holds for "count + 1".
         This goal contains "seq f (count + 1) start", so we know that we're in
         the recursive case of "seq", so we'd like to replace "seq f (count + 1)
         start" by the recursive case we wrote in its definition.  Unfortunately,
         neither "unfold seq" nor "simplify" can do this, but the tactic
         "unfold_recurse F k", where F is the function in question and k its
         argument, does the job: *)
      unfold_recurse (seq f) count.
      (* And here's a hint you'll need later: Sometimes, your goal won't exactly
         contain (seq f (count + 1) start), but maybe (seq f someOtherExpression
         start), but you still know that someOtherExpression is strictly greater
         than 0.  In such cases, if you want to use "unfold_recurse", you first
         have to run

         <<<
         replace someOtherExpression with (someOtherExpression - 1 + 1) by
         linear_arithmetic.
         >>>

         Note that if someOtherExpression could be 0, this won't work, because
         subtraction on natural numbers in Coq returns 0 if the result is
         negative, so "0 - 1 + 1" equals 1 in Coq's natural numbers, and
         linear_arithmetic can't prove "0 = 1" for you! *)

      simplify. rewrite IHcount. linear_arithmetic.
  Qed.

  (* And here's another general hint: You don't always need induction.  Some lemmas
     in this pset can be solved using induction but don't actually require it
     and are simpler to solve if you don't use induction, so before doing
     induction, try to think where/if you would need an inductive hypothesis. *)

  (* Exercise: Prove that the i-th element of seq has the value we'd expect. *)
  Lemma seq_spec: forall f count i start, i < count -> ith i (seq f count start) = f (start + i).
  Proof.
    induct count; simplify.
      linear_arithmetic.
      
      unfold_recurse (seq f) count.
      case_eq i. {
        simplify.
        replace (start + 0) with start by linear_arithmetic.
        equality.
      } {
        intro p.
        intro.
        replace (N.pos p) with ((N.pos p) - 1 + 1) by linear_arithmetic.
        unfold_recurse ith ((N.pos p) - 1).
        replace (start + (N.pos p - 1 + 1)) with ((start + 1) + (N.pos p - 1)) by linear_arithmetic.
        apply (IHcount (N.pos p - 1) (start + 1)).
        linear_arithmetic.
      }
  Qed.

  (* Exercise: Prove that if the index is out of bounds, "ith" returns 0. *)
  Lemma ith_out_of_bounds_0: forall i l, len l <= i -> ith i l = 0.
  Proof.
    induct i. {
      intro l.
      cases l. {
        simplify.
        equality.
      } {
        simplify.
        assert (1 + len l > 0) by linear_arithmetic.
        contradiction.
      }
    } {
      unfold_recurse ith i.
      intro l.
      cases l. {
        equality.
      } {
        simplify.
        assert (len l <= i) by linear_arithmetic.
        apply (IHi l H0).
      }
    }
  Qed.


  (* Binomial coefficients *)
  (* ********************* *)

  (* You might remember binomial coefficients from your math classes. They appear in many combinatorics
     problems and form the coefficients of the expansion of the polynomial (x + y)^n.
     In math notation, they are defined as follows:

        / n \        n!
        |   |  = ---------
        \ k /    (n-k)! k!

     We can transcribe this to Coq as follows: *)

  Definition C(n k: N): N := n! / ((n - k)! * k!).

  (* If we want to know how many ways there are to pick 2 items out of 4 items, we
     can compute this in Coq: *)
  Compute C 4 2.

  (* And here are the coefficients of the expansion of (x + y)^3: *)
  Compute [C 3 0; C 3 1; C 3 2; C 3 3].

  (* For larger numbers, however, this way of computing C becomes quite slow:

  Compute C 1000 100.

     \u2026takes about 2 seconds on my computer. You can measure the time by putting
     "Time" in front of any command:

  Time Compute C 1000 100.

     In the fraction defining C, there are many factors which appear both in the
     numerator and in the denominator, so it seems that we should be able to
     cancel these out and write a more efficient implementation of C. Here is one
     candidate: *)

  Definition bcoeff(n: N): N -> N :=
    recurse by cases
    | 0 => 1
    | k + 1 => recurse * (n - k) / (k + 1)
    end.

  (* Now if we do

  Time Compute bcoeff 1000 100.

     it only takes about 0.02 seconds on my computer, so we got a 100x speed
     improvement, yay!  But how do we know whether it's correct?  We could do some
     quick tests: *)

  Compute [bcoeff 3 0; bcoeff 3 1; bcoeff 3 2; bcoeff 3 3].

  (* This test produces the same values as for C, but we want to be sure that
     bcoeff will *always* produce the same values as C, so let's prove it,
     i.e. let's show that

     forall n k, k <= n -> bcoeff n k = C n k

     We will do so further below, but we first need a few helper lemmas and
     techniques:

     Many arithmetic goals in this pset are linear, i.e. there are only
     multiplications by constants but no multiplications of two variables.  For
     these linear-arithmetic goals, the linear_arithmetic tactic works just fine,
     but for some non-linear goals which will appear in this Pset, you can try the
     tactic "nia" (which stands for "non-linear integer arithmetic"), but it does
     not always work, so sometimes you will have to search for appropriate lemmas
     to apply manually.  For instance, to prove the following: *)
  Goal forall n m, n <> 0 -> m <> 0 -> n * m <> 0.
  Proof.
    simplify.
    (* you could use the "Search" command with a pattern: *)
    Search (_ * _ <> 0).
    (* which outputs the name of a handy lemma we can apply: *)
    apply N.neq_mul_0.
    split; assumption.
    (* (Note that in this case "nia" would have worked as well, but in any case, it's good to know
       the "Search" command.) *)
  Qed.

  (* Here's another example of how to use the "Search" command: Suppose you have
     the goal *)
  Goal forall n, n <> 0 -> n / n = 1.
  Proof.
    simplify.
    (* If we do "Search (_ / _)" we get a very long list, but if we do *)
    Search (?x / ?x).
    (* we force the two numbers on both sides of the / to be the same, and we only get the lemma we need: *)
    apply N.div_same.
    assumption.
  Qed.

  (* Now we're ready to prove a few simple facts: *)

  Lemma fact_nonzero: forall n, n! <> 0.
  Proof.
    induct n. {
      simplify.
      equality.
    } {
      unfold_recurse fact n.
      apply N.neq_mul_0.
      linear_arithmetic.
    }
  Qed.

  Lemma Cn0: forall n, C n 0 = 1.
  Proof.
    unfold C.
    induct n. {
      simplify.
      Search (1 * ?x = ?x).
      rewrite N.mul_1_l.
      apply N.div_same.
      equality.
    } {
      unfold_recurse fact n.
      replace (n + 1 - 0) with (n - 0 + 1) by linear_arithmetic.
      unfold_recurse fact (n - 0).
      replace (n - 0 + 1) with (n + 1) by linear_arithmetic.
      Search ((?x * ?y) / (?x * ?z) = ?y / ?z).
      replace ((n + 1) * (n - 0)! * 0!) with ((n + 1) * ((n - 0)! * 0!)) by linear_arithmetic.
      rewrite (N.div_mul_cancel_l (n!) ((n - 0)! * 0!) (n + 1)). {
        assumption.
      } {
        apply N.neq_mul_0.
        split.
        apply fact_nonzero.
        apply fact_nonzero.
      } {
        linear_arithmetic.
      }
    }
  Qed.

  Lemma Cnn: forall n, C n n = 1.
  Proof.
    unfold C.
    intro n.
    replace (n - n) with 0 by linear_arithmetic.
    simplify.
    rewrite N.mul_1_l.
    apply N.div_same.
    apply fact_nonzero.
  Qed.


  (* It's somewhat surprising that in the definition of C(n, k),

        n!
    -----------
    (n - k)! k!

    the denominator always divides the numerator.
    The following lemma proves it. Note that "(a | b)" means "a divides b".  We
    provide the solution for you, so that you can step through it and use it as a
    source of useful strategies you can apply in the exercises below.  Make sure
    to step through it and to understand each proof step! *)
  Lemma C_is_integer: forall n k, k <= n ->
      (((n - k)! * k!) | n!).
  Proof.
    induct n; simplify.

    - replace k with 0 by linear_arithmetic.
      Search (1 * _).
      rewrite N.mul_1_l; simplify.
      Search (?a | ?a).
      apply N.divide_refl.

    - (* We want to use the induction hypothesis, but it is not directly
         applicable to [k], since [k] could be equal to [n + 1]. *)
      assert (k = 0 \/ k = n + 1 \/ 0 < k <= n) as Hk by linear_arithmetic;
        cases Hk; subst; simplify.

      + rewrite N.sub_0_r, N.mul_1_r.
        apply N.divide_refl.

      + rewrite N.sub_diag; simplify.
        rewrite N.mul_1_l.
        apply N.divide_refl.

      + (* The key idea is to use the induction hypothesis twice. *)
        assert (k <= n) as Hle by linear_arithmetic.
        pose proof (IHn k Hle) as Hdk.

        assert (k - 1 <= n) as Hle1 by linear_arithmetic.
        pose proof (IHn (k - 1) Hle1) as Hdk1.

        (* How can we use facts about divisibility?
           Unfolding the definition helps: *)
        (* Locate "|". (* Notation "( p | q )" := (N.divide p q) *) *)
        (* unfold N.divide in *. *)

        (* [invert] will give us a concrete value instead of an existential: *)
        (* invert Hdk; invert Hdk1. *)

        (* Next we proceed to harmonize the divisors to be able to sum them. *)
        Search (_ * _ | _ * _).

        (* The first equation is missing a (n - k + 1) factor *)
        apply N.mul_divide_mono_l with (p := n + 1 - k) in Hdk.
        replace ((n + 1 - k) * ((n - k)! * k!))
          with ((n + 1 - k)! * k!) in Hdk; cycle 1.
        { replace (n + 1 - k) with (n - k + 1) by linear_arithmetic.
          unfold_recurse fact (n - k).
          replace (n - k + 1) with (n + 1 - k) by linear_arithmetic.
          linear_arithmetic. }

        (* The second is missing a (k) factor *)
        apply N.mul_divide_mono_l with (p := k) in Hdk1.
        replace (n - (k - 1)) with (n + 1 - k) in Hdk1
          by linear_arithmetic.
        replace (k * ((n + 1 - k)! * (k - 1)!))
          with ((n + 1 - k)! * k!) in Hdk1; cycle 1.
        { replace k with (k - 1 + 1) at 2 by linear_arithmetic.
          unfold_recurse fact (k - 1).
          replace (k - 1 + 1) with k by linear_arithmetic.
          linear_arithmetic. }

        (* Now we can sum the equations: *)
        Search (_ | _ + _).
        pose proof N.divide_add_r _ _ _ Hdk Hdk1 as Hd.
        replace ((n + 1 - k) * n! + k * n!) with ((n + 1)!) in Hd; cycle 1.
        { unfold_recurse fact n. nia. }

        equality.
  Qed.

  (* Now we're ready to prove correctness of our optimized implementation bcoeff.
     Since this is not a class about math, we're providing a paper proof of each
     proof step of the inductive case:

    C(n, k + 1)

               n!
  = -----------------------
    (n - (k + 1))! (k + 1)!

               n!
  = -----------------------
    (n - k - 1)! k! (k + 1)

           n! (n - k)
  = -------------------------------
    (n - k - 1)! (n - k) k! (k + 1)

                 n! (n - k)
  = ---------------------------------------
    (n - k - 1)! (n - k - 1 + 1) k! (k + 1)

            n! (n - k)
  = ---------------------------
    (n - k - 1 + 1)! k! (k + 1)

        n! (n - k)
  = -------------------
    (n - k)! k! (k + 1)

    n! (n - k)
  = ----------- / (k + 1)
    (n - k)! k!

        n!
  = ----------- * (n - k) / (k + 1)
    (n - k)! k!

  = C(n, k) * (n - k) / (k + 1)

  = bcoeff(n, k) * (n - k) / (k + 1)

  = bcoeff(n, k + 1)

  Your task is to translate this proof into Coq!

  Potentially useful hint:
  Note that multiplication and division have the same operator priority, and both
  are left-associative, so
     "a / b * c / d" is "((a / b) * c) / d", NOT "(a / b) * (c / d)"

  Here we go: *)

  Lemma fact_nonzero_2: forall k1 k2: N, k1! * k2! <> 0.
  Proof.
    intros k1 k2.
    apply N.neq_mul_0.
    split.
    all: apply fact_nonzero.
  Qed.
    
  Lemma bcoeff_correct: forall n k, k <= n -> bcoeff n k = C n k.
  Proof.
    induct k; simplify. {
      rewrite Cn0.
      equality.
    } {
      (* step 1 *)
      unfold C.
      (* step 2 *)
      unfold_recurse fact k.
      (* step 3 *)
      rewrite <- (N.div_mul_cancel_l (n!) ((n - (k + 1))! * ((k + 1) * k!)) (n - k)). {
        (* step 4-6 *)
        rewrite N.mul_assoc.
        rewrite N.mul_assoc.
        assert ((n - k)! = (n - k) * (n - (k + 1))!). {
          replace (n - (k + 1)) with (n - k - 1) by linear_arithmetic.
          replace (n - k) with (n - k - 1 + 1) by linear_arithmetic.
          unfold_recurse fact (n - k - 1).
          replace (n - k - 1 + 1 - 1) with (n - k - 1) by linear_arithmetic.
          equality.
        }
        rewrite <- H0.
        (* step 7 *)
        Search (_ / _ / _).
        replace ((n - k)! * (k + 1) * k!) with ((n - k)! * k! * (k + 1)) by linear_arithmetic.
        rewrite <- (N.div_div ((n - k) * n!) ((n - k)! * k!) (k + 1)). {
          (* step 8 *)
          Search ((_ / _) * _ = _ * (_ / _)).
          Search (?x * ?y / ?y).
          Search (?y * (?x / ?y)).
          destruct (C_is_integer n k) as (x, Hx). {
            linear_arithmetic.
          }
          rewrite Hx.
          Search (_ * (_ * _)).
          rewrite N.mul_assoc.
          rewrite N.div_mul by (apply fact_nonzero_2).
          rewrite N.mul_comm.
          rewrite <- (N.div_mul x ((n - k)! * k!)) by (apply fact_nonzero_2).
          rewrite <- Hx.
          (* step 9 *)
          fold (C n k).
          (* step 10 *)
          rewrite <- IHk by linear_arithmetic. 
          (* step 11 *)
          unfold_recurse (bcoeff n) k.
          equality.
        } {
          apply fact_nonzero_2.
        } {
          linear_arithmetic.
        }
      } {
        apply N.neq_mul_0.
        split. {
          apply fact_nonzero.
        } {
          apply N.neq_mul_0.
          split. {
            linear_arithmetic.
          } {
            apply fact_nonzero.
          }
        }
      } {
        linear_arithmetic.
      }
    }

  Qed.


  (* All binomial coefficients for a given n *)
  (* *************************************** *)

  (* In some applications, we need to know all binomal coefficients C(n,k) for a fixed n.
     For instance, if we want to symbolically evaluate (x + y)^4, the result is

     C(4,0)*x^4 + C(4,1)*x^3*y + C(4,2)*x^2*y^2 + C(4,3)*x*y^3 + C(4,4)*y^4

     The simplest way to compute such lists would be to just use the C we defined above: *)

  Definition all_coeffs_slow1(n: N): list N :=
    (recurse by cases
     | 0 => [1]
     | k + 1 => C n (k + 1) :: recurse
     end) n.

  Compute all_coeffs_slow1 0.
  Compute all_coeffs_slow1 1.
  Compute all_coeffs_slow1 2.
  Compute all_coeffs_slow1 3.
  Compute all_coeffs_slow1 4.
  Compute all_coeffs_slow1 5.
  Compute all_coeffs_slow1 15.
  (* However, this is not very efficient:

  Time Compute all_coeffs_slow1 100.

  takes 0.8s on my machine *)

  (* We could use our more efficient bcoeff from above: *)
  Definition all_coeffs_slow2(n: N): list N :=
    (recurse by cases
     | 0 => [1]
     | k + 1 => bcoeff n (k + 1) :: recurse
     end) n.

  Compute all_coeffs_slow2 5.
  Compute all_coeffs_slow2 15.
  (* This is faster:

     Time Compute all_coeffs_slow2 100.

  takes 0.2s on my machine and

    Time Compute all_coeffs_slow2 200.

  takes 1.7 s on my machine.

  But we can do even better by using Pascal's triangle:

        1
       1 1
      1 2 1
     1 3 3 1
    1 4 6 4 1

  You can observe that the i-th row of this triangle is the result of
  "all_coeffs_slow1 i", and that each value not at the boundary of the triangle is
  the sum of the values to its upper left and its upper right. For instance, the 6
  in the last row is the sum of the two 3s above it.
  More formally, we can state this as follows: *)
  Definition Pascal's_rule: Prop := forall n k,
      1 <= k <= n ->
      C (n+1) k = C n (k - 1) + C n k.
  (* Note that the above is only a definition which gives a name to this
     proposition but not a lemma.  We don't ask you to prove it, but it's a fun
     optional exercise; have a look at the end of this file if you're
     interested! *)

  (* The following function takes in a line of Pascal's triangle and computes the
     line below it: *)
  Definition nextLine(l: list N): list N :=
    1 :: seq (fun k => ith (k - 1) l + ith k l) (len l) 1.

  Compute nextLine [1; 3; 3; 1].
  Compute nextLine (nextLine [1; 3; 3; 1]).

  (* This allows us to define a faster all_coeffs function: *)
  Definition all_coeffs_fast: N -> list N :=
    recurse by cases
    | 0 => [1]
    | n + 1 => nextLine recurse
    end.

  (* Time Compute all_coeffs_fast 200. takes 0.35s on my computer *)


  (* Exercise: Let's prove that all_coeffs_fast is correct.
     Note that you can assume Pascal's rule to prove this. *)
  (* HINT 1 (see Pset2Sig.v) *)
  Lemma all_coeffs_right_length: forall n, len (all_coeffs_fast n) = n + 1.
  Proof.
    induct n. {
      simplify.
      linear_arithmetic.
    } {
      unfold_recurse all_coeffs_fast n.
      simplify.
      rewrite seq_len.
      rewrite IHn.
      linear_arithmetic.
    }
  Qed.

  Lemma all_coeffs_fast_correct:
    Pascal's_rule ->
    forall n k,
      k <= n ->
      ith k (all_coeffs_fast n) = C n k.
  Proof.
    intro pascals_rule.
    induct n. {
      simplify.
      unfold C.
      case_eq k. {
        simplify.
        rewrite N.mul_1_l.
        rewrite N.div_same.
        { equality. } { discriminate. }
      } {
        simplify.
        linear_arithmetic.
      }
    } {
      unfold_recurse all_coeffs_fast n.
      unfold nextLine.
      intro k.
      cases k. {
        simplify.
        rewrite Cn0.
        equality.
      } {
        unfold_recurse ith k.
        intro.
        rewrite seq_spec. {
          rewrite (IHn (1 + k - 1)) by linear_arithmetic.
          assert (k = n \/ k < n) as Hk by linear_arithmetic.
          cases Hk. {
            rewrite Hk.
            rewrite ith_out_of_bounds_0. {
              replace (1 + n - 1) with n by linear_arithmetic.
              rewrite Cnn.
              rewrite Cnn.
              linear_arithmetic.
            } {
              rewrite all_coeffs_right_length.
              linear_arithmetic.
            }
          } {
            rewrite IHn by linear_arithmetic.
            replace (k + 1) with (1 + k) by linear_arithmetic.
            rewrite (pascals_rule n (1 + k)) by linear_arithmetic.
            equality.
          }
        } {
          rewrite all_coeffs_right_length.
          linear_arithmetic.
        }
      }
    }
  Qed.

  (* ----- THIS IS THE END OF PSET2 ----- All exercises below this line are optional. *)

  (* Optional exercise: Let's prove that Pascal's rule holds.
     On paper, this can be proved as follows, but feel free to ignore this if you want
     the full challenge!

     C(n, k-1) + C(n, k)

             n!                 n!
  = --------------------- + -----------
    (n - k + 1)! (k - 1)!   (n - k)! k!

                n!                          n!
  = ----------------------------- + -------------------
    (n - k)! (n - k + 1) (k - 1)!   (n - k)! k (k - 1)!

                 n! k                          n! (n - k + 1)
  = ------------------------------- + -------------------------------
    (n - k)! (n - k + 1) (k - 1)! k   (n - k)! k (k - 1)! (n - k + 1)

           n! (k + n - k + 1)
  = -------------------------------
    (n - k)! (n - k + 1) (k - 1)! k

      (n + 1)!
  = ---------------
    (n - k + 1)! k!

  = C(n+1, k)
  *)
  Lemma Pascal's_rule_holds: Pascal's_rule.
  Proof.
    unfold Pascal's_rule.

    (* Note: Proving
         a     b     a+b
        --- + --- =  ---
         c     c      c
       is a bit trickier than you might expect, because we're using integer division here.
       So, for instance,
        1     3                                                              1+3
       --- + ---   equals 0 + 1 in round-down integer division, which is not ---
        2     2                                                               2
       To make sure this rule holds, we must also require that c and b both divide a: *)
    assert (forall a b c, c <> 0 -> (c | a) -> (c | b) -> a / c + b / c = (a + b) / c)
      as add_fractions. {
      clear.
      simplify.
      unfold N.divide in *. invert H0. invert H1.
      rewrite N.div_mul by assumption.
      rewrite N.div_mul by assumption.
      replace (x * c + x0 * c) with ((x + x0) * c) by nia.
      rewrite N.div_mul by assumption.
      reflexivity.
    }

  Admitted.

  (* Optional exercise:
     all_coeffs_fast is still not as fast as it could be, because nextLine uses ith
     to access the elements of the previous line, and each invocation of ith takes
     linear time in i.
     It would be more efficient to implement nextLine as a recursive function
     which iterates through the previous line just once and computes the next line
     on the fly.
     Define such a nextLine' function, and then use it to define all_coeffs_faster,
     observe how it's even faster than all_coeffs_fast, and finally, prove that
     it's correct. *)

  Definition nextLine'(l: list N): list N. Admitted.

  Definition all_coeffs_faster: N -> list N. Admitted.

  Lemma all_coeffs_faster_correct: forall n k,
      k <= n ->
      ith k (all_coeffs_faster n) = C n k.
  Proof.
  Admitted.
End Impl.

Module ImplCorrect : Pset2Sig.S := Impl.

(*|
TIPS: A few things to keep in mind as you work through pset 2
=============================================================
|*)


Require Import Coq.NArith.NArith.
Open Scope N_scope.
Require Import Frap.Frap.
Import Pset2.Impl.

Notation "x !" := (fact x) (at level 12, format "x !"). (* local in Pset2 *)

(* Here we demonstrate a number of useful Coq tactics.  Step though the
   examples, and check Coq's reference manual or ask us in office hours if
   you're confused about any of these tactics.

   These are not exercises, just neat examples; feel free to work on it at your
   pace over multiple psets and to refer to it at later points; no need to go
   through it all at once.  *)

(* The tactic we introduce in each example is underlined like this. *)
                                             (********************)

Parameter whatever: Prop.

(* \u2018apply\u2019 matches the conclusion of a theorem to the current goal, then
   replaces it with one subgoal per premise of that theorem: *)

Goal forall (P Q R: Prop) (H1: P) (H2: Q) (IH: P -> Q -> R), R.
Proof.
  simplify.
  apply IH.
 (********)
Abort.

(* Apply works with implications (`A -> B`) but also with equivalences, where
   it tries to pick the right direction based on the goal: *)
Goal forall (n m k: N), n = m.
Proof.
  simplify.
  Check N.mul_cancel_r.

  (* Careful: apply only works if it's clear how the theorem applies to your goal: *)
  Fail apply N.mul_cancel_r.
  (* Here, Coq wants to know the value of \u2018p\u2019 before it can apply the lemma; so,
     we use the \u2018with\u2019 for of \u2018apply\u2019 to supply it: *)
  apply N.mul_cancel_r with (p := n - k + 1).
 (****)               (****)
Abort.

(* Apply also works in hypotheses, where it turns premises into conclusions: *)
Goal forall (n m k: N), n = m -> whatever.
Proof.
  simplify.
  apply N.mul_cancel_r with (p := n - k + 1) in H.
 (*****)              (****)                (**)
Abort.

Goal forall (n m k: N), n - k + 1 <> 0 -> n = m -> whatever.
Proof.
  simplify.

  (* Specifying parameters by hand is not always convenient, so we can ask Coq
     to create placeholders instead, to be filled later: *)
  eapply N.mul_cancel_r in H0.
 (******)              (**)
  2: { (* This \u20182:\u2019 notation means: operate on the second goal *)
    apply H.
  } (* \u2026 and the curly braces delimit a subproof. *)
Abort.

Goal forall (P Q R S: Prop), (P -> S) -> (R -> S) -> P \/ Q \/ R -> S.
Proof.
  simplify.
  cases H1. (* You are familiar with \u2018cases\u2019 from pset 1. *)
 (*****)
  - apply H. apply H1.
  - admit. (* \u2018admit\u2019 is just like \u2018Admitted\u2019 but for a single goal *)
   (*****)
  - apply H0. apply H1.
Fail Qed. (* But if you use \u2018admit\u2019, no \u2018Qed\u2019 for you! *)
Admitted.

(* Here is a convenient pattern that you will be familiar with from math
   classes.  It's called a \u201ccut\u201d.  We state an intermediate fact and prove it
   as part of a larger proof. *)

Goal forall (f : N -> N) (count : N)
       (IHcount : forall i start : N, i < count ->
                                 ith i (seq f count start) = f (start + i))
       (i start : N)
       (H : i < count + 1),
  ith i (f start :: seq f count (start + 1)) = f (start + i).
Proof.
  simplify.

  (* \u2018assert\u2019 introduces the fact that we want to prove, then uses *)
  assert (i = 0 \/ 0 < i) as A. { (* the \u2018as\u2019 clause to name the resulting fact *)
 (******)                (**)
    linear_arithmetic.          (* The proof of the lemma comes first. *)
  }
  cases A.                      (* Then we get to use the lemma itself. *)
  - subst. (* \u2018subst\u2019 rewrites all equalities. *)
   (*****)  (* or "subst i" for just one var *)
    simplify. admit.
  - (* Another assertion! This time we fit the whole proof in a \u2018by\u2019 clause. *)
    assert (i = i - 1 + 1) as E by linear_arithmetic.
   (******)                    (**)
    rewrite E.
    unfold_recurse ith (i - 1).
Abort.

Goal forall (n x0 k: N),
    0 < k ->
    k + 1 < n ->
    n! = x0 * ((n - (k - 1))! * (k - 1)!) ->
    whatever.
Proof.
  intros n m.
 (******)
  (* \u2018simplify\u2019 takes care of moving variables into the \u201ccontext\u201d above the
     line, but \u2018intros\u2019 gives finer grained control and lets you name
     hypotheses.  Users of Proof General with company-coq can type \u2018intros!\u2019 to
     get names automatically inserted. *)
  intros. (* A plain \u2018intros\u2019 takes care of all remaining variables. *)
  (******)

  (* Sometimes we want to say \u201ca = b, so replace all \u2018a\u2019s with \u2018b\u2019s.\u201d.  Replace
     is the perfect tactic for these cases; it's like \u2018assert\u2019 followed by
     \u2018rewrite\u2019. *)
  replace (n - (k - 1)) with (n - k + 1) in H1 by linear_arithmetic.
 (*******)             (****)           (**)  (**)
  (* "in" and "by" are optional *)
  unfold_recurse fact (n - k).
Abort.

Goal forall (P Q R: Prop) (H0: Q) (x: N) (H: forall (a b: N), P -> Q -> a < b -> R), whatever.
Proof.
  simplify.
  (* Often you have a general hypothesis, and you want to make it more specific
     to your case.  Then, \u2018specialize\u2019 is the tactic you want: *)
  specialize H with (b := x).
 (**********) (****)
  assert (3 < x) by admit.
  specialize H with (2 := H0) (3 := H1).
Abort.

Goal forall (f : N -> N) (start : N),
    f start = f (start + 0).
Proof.
  simplify.

  (* We have seen \u2018apply\u2019 earlier, which applies a theorem ending with an
     implication to a complete goal.  \u2018rewrite\u2019 takes a theorem ending in an
     equality and replaces matching subterms of the goal according to that
     equality: *)
  rewrite N.add_0_r.
 (*******)
  (* Options like "with (a := 2)", "in H", "by tactic" also work! *)
  equality.
Abort.

Goal forall (f : N -> N) (start : N),
    f start = f (start + 0).
Proof.
  simplify.
  (* Alternatively, sometimes, it helps to apply the principle that, if two
     function arguments match, then the function calls themselves match: *)
  f_equal.
 (*******)
  linear_arithmetic.
Abort.

Goal forall (f : N -> N) (start : N),
    f start = f (start + 0).
Proof.
  simplify.
  (* How many other ways can we find to deal with this theorem? *)
  assert (start + 0 = start) as E by linear_arithmetic.
  rewrite E.
Abort.

Goal forall (A B: Type) (f: A -> B) (a1 a2 a3: A),
    Some a1 = Some a2 ->
    Some a2 = Some a3 ->
    f a3 = f a1.
Proof.
  (* \u2018simplify\u2019 is a favorite of this class, which does all sorts of small goal
     reorganization to make things more readable. *)
  simplify.

  (* \u2018invert\u2019 is another favorite: it \u201creplaces hypothesis H with other facts that can be deduced from the structure of H's statement\u201d.

     Specifically, it looks at the structure of the arguments passed to the
     constructors of inductive types appearing in H and deduces equalities from
     that and then substitutes the equalities.  It's also particularly useful
     for inductive \u2018Prop\u2019s, which we will see later in this class. *)
  invert H. (* Watch what happens carefully in this example *)
 (******)
  invert H0.
  equality.
Abort.

Goal forall (A B: Type) (f: A -> B) (a1 a2 a3: A),
    Some a1 = Some a2 ->
    Some a2 = Some a3 ->
    f a3 = f a1.
Proof.
  simplify.
  equality. (* Of course, \u2018equality\u2019 can do all the work for us here. *)
 (********)
Abort.

Goal forall (a1 a2 b1 b2: N) (l1 l2: list N),
    a1 :: b1 :: l1 = a2 :: b2 :: l2 ->
    a1 = a2 /\ b1 = b2 /\ l1 = l2.
Proof.
  simplify.
  (* \u2018invert\u2019 works at arbitrary depth, btw: *)
  invert H.
 (******)
Abort.

(* If you ever end up with contradictory hypotheses, you'll want to apply the
   pompously named \u201cex falso quodlibet\u201d principle (also known under the
   scary-sounding name of \u201cprinciple of explosion\u201d), through the aptly named
   \u2018exfalso\u2019 tactic: *)
Goal forall (P: Prop) (a b: N),
    (a < b -> ~P) ->
    P ->
    whatever.
Proof.
  simplify.
  assert (a < b \/ b <= a) as C by linear_arithmetic. cases C.
  - exfalso.
   (*******)
    unfold not in H.
    apply H.
    all: assumption.
Abort.

(* Contradictions can take many forms; a common one is Coq is an impossible equality between two constructors; here the empty list \u2018[]\u2019 and a nonempty list \u2018a :: l\u2019. *)
Goal forall (a : N) (l : list N),
    a :: l = [] ->
    whatever.
Proof.
  simplify.
  discriminate.
 (************)
Abort.

Goal forall (P Q R S T: Prop), (P \/ Q -> T) -> (R \/ S -> T) -> P \/ S -> T.
Proof.
  simplify.
  cases H1.
  - apply H. left. assumption.
  - apply H0. right. assumption.
Abort.

(* Here are some more interesting tactics to look into along your Coq journey.
   Happy proving!

   - constructor, econstructor
   - eassumption
   - eexists
   - first_order
   - induct
   - left, right
   - trivial
   - transitivity
   - symmetry
*)

(* References:

   - FRAP book Appendix A.2. Tactic Reference (http://adam.chlipala.net/frap/frap_book.pdf)
   - Coq Reference Manual, Chapter on Tactics (https://coq.inria.fr/refman/proof-engine/tactics.html)
*)
