(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 5 *)

Require Import Frap.Frap Pset5.Pset5Sig.

Module Impl.
  (* In this pset, we will explore different ways of defining semantics for the
     simple imperative language we used in Chapter 4 (Interpreters.v) and
     Chapter 7 (OperationalSemantics.v).
     Make sure to reread these two files, because many definitions we ask you
     to come up with in this pset are similar to definitions in these two files.

     Pset5Sig.v contains the number of points you get for each definition and
     proof. Note that since we ask you to come up with some definitions
     yourself, all proofs being accepted by Coq does not necessarily guarantee a
     full score: you also need to make sure that your definitions correspond to
     what we ask for in the instructions. *)

  (* Our language has arithmetic expressions (note that we removed Times and Minus,
     because they don't add anything interesting for this pset): *)
  Inductive arith: Set :=
  | Const (n: nat)
  | Var (x: var)
  | Plus (e1 e2: arith).

  (* And it has commands, some of which contain arithmetic expressions: *)
  Inductive cmd :=
  | Skip
  | Assign (x: var) (e: arith)
  | Sequence (c1 c2: cmd)
  | If (e: arith) (thn els: cmd)
  | While (e: arith) (body: cmd).

  (* As in the lecture, we use a finite map to store the values of the variables: *)
  Definition valuation := fmap var nat.

  (** * Part 1: Using a recursive function **)

  (* To make it a bit more interesting, we add a twist:
     If an arithmetic expression reads an undefined variable, instead of just
     returning 0, we specify that an arbitrary value can be returned.
     Therefore, the signature we used in class,

       Fixpoint interp (e: arith) (v: valuation): nat :=
         ...

     will not work any more, because that one can only return one value.
     Instead, we will use the following definition: *)

  Fixpoint interp (e: arith) (v: valuation) (retval: nat): Prop :=
    match e with
    | Const n => retval = n
    | Var x =>
      match v $? x with
      | None => True (* any retval is possible! *)
      | Some n => retval = n
      end
    | Plus e1 e2 =>
      exists a1 a2,
      interp e1 v a1 /\
      interp e2 v a2 /\
      retval = a1 + a2
    end.
  (* You can read [interp e v retval] as the claim that "interpreting expression
     e under the valuation v can return the value retval".
     And if we don't provide the last argument, we can think of "interp e v",
     which has type "nat -> Prop", as "the set of all possible values e could
     return". *)

  (* Let's look at some examples: *)

  (* The only result allowed by [Const 3] is [3]: *)
  Compute interp (Const 3) _.

  (* If we interpret the expression "y + z" in a valuation where
     y is 2 and z is 3, then the only possible result is 5. *)

  Goal forall retval,
      interp (Plus (Var "y") (Var "z"))
             ($0 $+ ("y", 2) $+ ("z", 3))
             retval <->
      retval = 5.
  Proof.
    simplify; propositional.
    - cases H; cases H.
      linear_arithmetic.
    - exists 2, 3.
      propositional.
  Qed.

  (* We can also look at this in terms of a partial application: *)

  Goal interp (Plus (Var "y") (Var "z"))
              ($0 $+ ("y", 2) $+ ("z", 3)) =
       (fun retval => retval = 5).
  Proof.
    simplify.
    apply sets_equal; simplify; propositional.
    - cases H; cases H.
      linear_arithmetic.
    - exists 2, 3.
      propositional.
  Qed.

  (* But if we leave [z] unset in the valuation, then [Var "z"] can return any
     value, and hence the complete program can return any value greater than or
     equal to 2. *)
  Goal interp (Plus (Var "y") (Var "z")) ($0 $+ ("y", 2)) = (fun retval => 2 <= retval).
  Proof.
    simplify.
    apply sets_equal.
    propositional.
    - cases H. cases H. linear_arithmetic.
    - exists 2, (x - 2). linear_arithmetic.
  Qed.

  (* Hint that will be useful later:
     In the above proof, you can see how you can deal with existentials:
     - If you have an [H: exists x, P] above the line, you can "cases H"
       to obtain such an "x" and "H: P".
     - If you have an [exists x, P] below the line, you can use "exists x0" to
       provide the value [x0] for which you want to prove the existential.
     Instead of repeating [cases], you can also use [first_order]. *)

  (** * Part 2: Using an inductive relation **)

  (* An alternative way of specifying how arithmetic expressions are evaluated
     is by using inference rules, where we put preconditions above the line,
     the conclusion below the line, and a name of the rule to the right of
     the line, using "Oxford brackets" to write statements of the form
     "a \u2208 \u27e6e\u27e7\u1d65" which we read as "the natural number a is in the set of
     values to which e can evaluate under the valuation v".
     If we were to write this on a blackboard, it might look like this:

                           n1 = n2
                        ------------ ValuesConst
                         n1 \u2208 \u27e6n2\u27e7\u1d65

                         (x \u21a6 a) \u2208 v
                        -------------- ValuesVarDefined
                           a \u2208 \u27e6x\u27e7\u1d65

                         x \u2209 dom(v)
                       ------------- ValuesVarUndefined
                         a \u2208 \u27e6x\u27e7\u1d65

            a1 \u2208 \u27e6e1\u27e7\u1d65   a2 \u2208 \u27e6e2\u27e7\u1d65   a=a1+a2
            ----------------------------------- ValuesPlus
                       a \u2208 \u27e6e1+e2\u27e7\u1d65

     Let's translate this to an Inductive Prop in Coq called "values". That is,
     [values e v a] should mean \u201cthe natural number a is in the set of
     values to which e can evaluate under the valuation v\u201d.

     Define an Inductive with four constructors, one for each of the four rules
     above, using the names written to the rights of the lines above as the
     constructor names.  We have included ValuesConst to give you a hint.
  *)
  Inductive values: arith -> valuation -> nat -> Prop :=
  | ValuesConst: forall v n1 n2,
      n1 = n2 ->
      values (Const n1) v n2
  | ValuesVarDefined: forall v x a,
      v $? x = Some a ->
      values (Var x) v a
  | ValuesVarUndefined: forall v x a,
      v $? x = None ->
      values (Var x) v a
  | ValuesPlus: forall v e1 e2 a1 a2 a,
      values e1 v a1 -> values e2 v a2 -> a1 + a2 = a ->
      values (Plus e1 e2) v a.


  (* Note that the following alternative would also work for ValuesConst and
     ValuesPlus:

                    ---------- ValuesConst
                     n \u2208 \u27e6n\u27e7\u1d65

            a1 \u2208 \u27e6e1\u27e7\u1d65     a2 \u2208 \u27e6e2\u27e7\u1d65
            --------------------------- ValuesPlus
                a1+a2 \u2208 \u27e6e1+e2\u27e7\u1d65

     But in Coq, this would be a bit less convenient, because the tactic
     [eapply ValuesPlus] would only work if the goal is of the shape
     [values _ _ (_ + _)], whereas if we add this extra equality,
     [eapply ValuesPlus] works no matter what the last argument to [values] is,
     and similarly for [ValuesConst]. *)

  (* Contrary to the Fixpoint-based definition "interp", we can't do simplification
     of the kind "replace interp by its body and substitute the arguments in it",
     because an Inductive Prop describes a family of proof trees and isn't a
     function with a right-hand side you could plug in somewhere else.
     In order to prove the example Goal from above for "values", we need to construct
     the following proof tree:

    ("y"\u21a62) \u2208 {"y"\u21a62}              "z" \u2209 dom({"y"\u21a62})
   -------------------- Defined    ----------------------- Undefined
    2 \u2208 \u27e6"y"\u27e7_{"y"\u21a62}               a-2 \u2208 \u27e6"z"\u27e7_{"y"\u21a62}              a=2+a-2
   ---------------------------------------------------------------------------- ValuesPlus
                        a \u2208 \u27e6"y"+"z"\u27e7_{"y"\u21a62}
  *)
  Example values_example: forall a,
      2 <= a ->
      values (Plus (Var "y") (Var "z")) ($0 $+ ("y", 2)) a.
  Proof.
    (* "simplify" only introduces the hypotheses but can't really simplify
       anything here. This is not a limitation of "simplify"; it's due to the
       way [values] is defined. *)
    simplify.
    (* Once you define the four constructors for "values", you can uncomment
       the script below. Make sure you understand how it relates to the proof
       tree above! *)
    
    eapply ValuesPlus with (a1 := 2) (a2 := a - 2).
    - eapply ValuesVarDefined. simplify. equality.
    - eapply ValuesVarUndefined. simplify. equality.
    - linear_arithmetic.
      
  Qed.

  (* Now, let's prove that "interp" and "values" are equivalent.
     First, [interp -> values]: *)
  Theorem interp_to_values: forall e v a,
      interp e v a -> values e v a.
  Proof.
    induct e.
    - simplify.
      apply ValuesConst.
      equality.
    - simplify.
      cases (v $? x).
      + apply ValuesVarDefined.
        equality.
      + apply ValuesVarUndefined.
        equality.
    - simplify.
      cases H.
      cases H.
      destruct H as (H1, (H2, H3)).
      apply (ValuesPlus v e1 e2 x x0).
      + apply IHe1.
        assumption.
      + apply IHe2.
        assumption.
      + equality.
  Qed.

  (* To prove the other direction, we have a choice: we can either induct on
     [e] or directly on the proof of [values e v a], because [values] is an
     inductively defined predicate.

     Let's do both proofs.  In general, inducting on the proof tree is the right
     approach, so let's start with that: *)
  Theorem values_to_interp: forall e v a,
      values e v a -> interp e v a.
  Proof.
    induct 1; (* \u2190 do not change this line *)
      simplify.
    - equality.
    - rewrite H.
      equality.
    - rewrite H.
      trivial.
    - exists a1.
      exists a2.
      auto.
  Qed.

  (* Now let's see how things look with an induction on e.  In this simple case,
     it's very similar: *)
  Theorem values_to_interp_induction_on_e: forall e v a,
      values e v a -> interp e v a.
  Proof.
    induct e; (* \u2190 not the best, but for the sake of the exercise do not change this line *)
      simplify;
      inversion H.
    - equality.
    - rewrite H1.
      equality.
    - rewrite H1.
      equality.
    - exists a1.
      exists a2.
      auto.
  Qed.

  (* Let's define nondeterministic big-step semantics for evaluating a command.
     Define [eval] as an Inductive Prop such that [eval v1 c v2] means
     "If we run command c on valuation v1, we can obtain valuation v2".
     Whenever you encounter an arithmetic expression, use [values] to obtain a
     value it can step to.
     Hint: This will be quite similar to [eval] in OperationalSemantics.v! *)
  Inductive eval: valuation -> cmd -> valuation -> Prop :=
  | EvalSkip: forall v,
      eval v Skip v
  | EvalAssign: forall v v' x e a,
      values e v a ->
      v' = v $+ (x, a) ->
      eval v (Assign x e) v'
  | EvalSequence: forall v v' v'' c1 c2,
      eval v c1 v' ->
      eval v' c2 v'' ->
      eval v (Sequence c1 c2) v''
  | EvalIfThen: forall v v' thn els e a,
      values e v a ->
      a <> 0 ->
      eval v thn v' ->
      eval v (If e thn els) v'
  | EvalIfElse: forall v v' thn els e,
      values e v 0 ->
      eval v els v' ->
      eval v (If e thn els) v'
  | EvalWhileContinue: forall v v' body e a,
      values e v a ->
      a <> 0 ->
      eval v (Sequence body (While e body)) v' ->
      eval v (While e body) v'
  | EvalWhileBreak: forall v body e,
      values e v 0 ->
      eval v (While e body) v.

  (* Hint: Many of the proofs below will depend on definitions we ask you to
     find yourself, and if you get these definitions wrong, the proofs will
     not work, so keep in mind that you might have to go back and adapt your
     definitions!
     Also, it can happen that many proofs go through and you become (overly)
     confident that your definitions are correct, even though they aren't. *)

  (* Here's an example program. If we run it on the empty valuation, reading the
     variable "oops" can return any value, but after that, no matter whether
     "oops" was zero or not, we assign a nonzero value to "tmp", so the answer
     will always be 42. *)
  Example the_answer_is_42 :=
    Sequence (Assign "x" (Var "oops"))
             (Sequence (If (Var "x")
                           (Assign "tmp" (Plus (Var "x") (Var "x")))
                           (Assign "tmp" (Const 1)))
                       (If (Var "tmp")
                           (Assign "answer" (Const 42))
                           (Assign "answer" (Const 24)))).

  (* To prove that this sample program always returns 42, we first prove a handy
     helper lemma (the [simplify] tactic will help with [$+]): *)
  Lemma read_last_value: forall x v c n,
      values (Var x) (v $+ (x, c)) n -> n = c.
  Proof.
    simplify.
    inversion H;
      simplify.
    - equality.
    - discriminate.
  Qed.

  (* Hint: This next theorem is a bit boring -- it's about 30 lines of "invert",
     "simplify", "discriminate", "equality", "linear_arithmetic" and
     "apply read_last_value in H", "subst" in our solution.

     But it's a good test case to make sure you got the definition of "eval"
     right! And note that inverting the hypotheses in the right order, i.e. in
     the order the program is executed, as well as using "read_last_value"
     whenever possible, will make your proof less long.



     (Or, you could use automation \u2014 our automated proof is 8 lines long.) *)

(* source: IntroToProofScripting *)
Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
      (* A hypothesis already asserts this fact. *)
    | _ =>
      match P with
        | ?P1 /\ ?P2 =>
          (* Check each conjunct of [P] separately, since they might be known by
           * different means. *)
          first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
          (* If we manage to get this far, then we found no redundancy, so
           * declare success. *)
      end
  end.

  Ltac find_invert :=
  match goal with
  | H : eval _ _ _ |- _ => invert H
  | H : values _ _ _ |- _ => invert H
  | H : Some ?x = Some ?y |- _ => notHyp (x = y); assert (x = y) by equality
  | _ => simplify; try linear_arithmetic; try equality
  end.

  Theorem the_answer_is_indeed_42:
    forall v, eval $0 the_answer_is_42 v -> v $? "answer" = Some 42.
  Proof.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    - find_invert.
      find_invert.
      + find_invert.
        find_invert.
        find_invert.
        * find_invert.
          find_invert.
          -- find_invert.
             ++ find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
             ++ find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
          -- find_invert.
             ++ find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
             ++ find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
        * find_invert.
          find_invert.
          -- find_invert.
             ++ find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
                ** find_invert.
                   find_invert.
                   --- find_invert.
                   --- find_invert.
      + find_invert.


    do 12 find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    simplify.
    find_invert.
    find_invert.
    find_invert.
    - simplify.
    find_invert.
      find_invert.
      find_invert.
    - find_invert.
    simplify.
    find_invert.
    simplify.
    find_invert.
    find_invert.
    find_invert.
    find_invert.
    find_invert.



    simplify.
    invert H.
    invert H3.
    invert H2. {
      simplify.
      discriminate.
    }
    invert H5.
    invert H3.
    - invert H5.
      + simplify.
        invert H6.
        * invert H11.
          simplify.
          invert H4.
          equality.
        * invert H9.
          invert H10.
          invert H4.
          invert H7.
          simplify.
          invert H3.
          invert H6.
          simplify.
          assert (a = a0) by equality.
          assert (a3 = a) by equality.
          assert (a4 = a) by equality.
          assert (a3 + a4 = 0) by equality.
          linear_arithmetic.

          simplify.
          assert (a = a0) by equality.
          assert (a3 = a) by equality.
          assert (a3 + a4 = 0) by equality.
          linear_arithmetic.

          
          simplify.
          assert (a = a0) by equality.
          assert (a4 = a) by equality.
          assert (a3 + a4 = 0) by equality.
          linear_arithmetic.

          simplify.
          discriminate.
      + simplify.
        discriminate.
    - invert H7.

      simplify.
      invert H8.
      invert H4.
      invert H6.

      invert H9.
      simplify.
      invert H4.
      equality.

      invert H8.
      simplify.
      invert H4.
      invert H7.

      simplify.
      discriminate.

      simplify.
      discriminate.

      simplify.
      discriminate.
  Qed.

  (* Here's another example program. If we run it on a valuation that is
     undefined for "x", it will read the undefined variable "x" to decide
     whether to abort the loop, so any number of loop iterations is possible. *)
  Example loop_of_unknown_length :=
    (While (Var "x") (Assign "counter" (Plus (Var "counter") (Const 1)))).

  (* Hint: you might need the "maps_equal" tactic to prove that two maps are the same. *)
  Theorem eval_loop_of_unknown_length: forall n initialCounter,
      eval ($0 $+ ("counter", initialCounter))
           loop_of_unknown_length
           ($0 $+ ("counter", initialCounter + n)).
  Proof.
    unfold loop_of_unknown_length.
    induct n; simplify.
    - assert (initialCounter + 0 = initialCounter) by linear_arithmetic.
      rewrite H.
      apply EvalWhileBreak.
      apply ValuesVarUndefined.
      simplify.
      equality.
    - apply EvalWhileContinue with (a := 1).
      + apply ValuesVarUndefined.
        simplify.
        equality.
      + discriminate.
      + apply EvalSequence with (v' := $0 $+ ("counter", initialCounter + 1)).
        * apply EvalAssign with (a := initialCounter + 1).
          -- apply ValuesPlus with (a1 := initialCounter) (a2 := 1).
             ++ apply ValuesVarDefined.
                simplify.
                equality.
             ++ apply ValuesConst.
                equality.
             ++ equality.
          -- maps_equal.
        * assert (initialCounter + S n = (initialCounter + 1) + n) by linear_arithmetic.
          rewrite H.
          apply IHn.
  Qed.

  (* Wherever this TODO_FILL_IN is used, you should replace it with your own code. *)
  Axiom TODO_FILL_IN: Prop.

  (** * Part 3: Fixpoints with fuel **)

  (* You might wonder whether we can use "Fixpoint" instead of "Inductive" to define
     such nondeterministic big-step evaluation of commands, and indeed we can.
     But we need some trick to convince Coq that this Fixpoint will always terminate,
     even though there could be infinite loops.

     We achieve this by using a "fuel" argument that limits the recursion depth.
     This does not exclude any possible final valuations, because for every final
     valuation, there exists a recursion depth sufficient to reach it.

     So let's define a Fixpoint [run] such that [run fuel v1 c v2] means
     "if we run command c on valuation v1 and limit the recursion depth to fuel,
     we can obtain valuation v2".

     We already defined all cases for you except the [While] case, but all the
     building blocks you need can be found in the other cases, too.
   *)
  Fixpoint run (fuel: nat) (v1: valuation) (c: cmd) (v2: valuation): Prop :=
    match fuel with
    | O => False
    | S fuel' =>
      match c with
      | Skip => v1 = v2
      | Assign x e => exists a, interp e v1 a /\ v2 = (v1 $+ (x, a))
      | Sequence c1 c2 => exists vmid, run fuel' v1 c1 vmid /\ run fuel' vmid c2 v2
      | If e c1 c2 =>
        (exists r, interp e v1 r /\ r <> 0 /\ run fuel' v1 c1 v2) \/
        (interp e v1 0 /\ run fuel' v1 c2 v2)
      | While e c1 =>
        (exists vmid r, interp e v1 r /\ r <> 0 /\ run fuel' v1 c1 vmid /\ run fuel' vmid (While e c1) v2) \/
        (interp e v1 0 /\ v1 = v2)
      end
    end.

  (* Now let's prove that [run] and [eval] are equivalent! *)

  Local Hint Constructors eval : core.

  Theorem run_to_eval: forall fuel v1 c v2,
      run fuel v1 c v2 ->
      eval v1 c v2.
  Proof.
    induct fuel.
    - simplify.
      contradiction.
    - simplify.
      cases c.
      + rewrite H.
        apply EvalSkip.
      + destruct H.
        destruct H.
        apply EvalAssign with (a := x0).
        * apply interp_to_values.
          assumption.
        * assumption.
      + destruct H.
        destruct H.
        apply EvalSequence with (v' := x).
        * apply IHfuel.
          assumption.
        * apply IHfuel.
          assumption.
      + propositional.
        * destruct H0.
          propositional.
          apply EvalIfThen with (a := x).
          -- apply interp_to_values.
             assumption.
          -- assumption.
          -- apply IHfuel.
             assumption.
        * apply EvalIfElse.
          -- apply interp_to_values.
             assumption.
          -- apply IHfuel.
             assumption.
      + propositional.
        * destruct H0.
          destruct H.
          propositional.
          apply EvalWhileContinue with (a := x0).
          -- apply interp_to_values.
             assumption.
          -- assumption.
          -- apply EvalSequence with (v' := x).
             ++ apply IHfuel.
                assumption.
             ++ apply IHfuel.
                assumption.
        * rewrite <- H1.
          apply EvalWhileBreak.
          apply interp_to_values.
          assumption.
  Qed.

  (* To prove the other direction, we will need the following lemma, which shows
     that excess fuel isn't an issue.

     Hint: Here, some proof automation might pay off!

     You could try writing a [repeat match goal] loop, to do all possible
     simplifications on your hypotheses and then use [eauto] to solve
     the goal. Maybe you need to increase the maximum search depth of eauto;
     in our solution, we had to write [eauto 9] instead of just [eauto],
     which defaults to [eauto 5].

     Some useful documentation pointers:
     - https://coq.inria.fr/refman/proofs/automatic-tactics/auto.html#coq:tacn.eauto
     - https://coq.inria.fr/refman/proof-engine/ltac.html?highlight=repeat#pattern-matching-on-goals-and-hypotheses-match-goal

     And note that [eauto] does not know about linear arithmetic by default,
     so you could consider registering it as a [Hint Extern], but a simpler
     way here would be to use the lemma "le_S_n" to turn "S fuel1 <= S fuel2"
     into "fuel1 <= fuel2", which will be needed for the IH. *)

Ltac solve_monotone :=
  simplify; propositional; match goal with
  | |- _ \/ _ => apply or_introl; solve_monotone
  | |- _ \/ _ => apply or_intror; solve_monotone
  | H : exists _, _ |- _ => destruct H; solve_monotone
  | x : valuation |- _ => exists x; solve_monotone
  | x : nat |- _ => exists x; solve_monotone
  | H : _ |- _ => apply H; solve_monotone
  | H : _ |- _ => apply H with (c := While _ _); solve_monotone
  | _ => assumption
  end.

  Lemma run_monotone_helper: forall fuel1 v1 c v2,
      run fuel1 v1 c v2 ->
      run (S fuel1) v1 c v2.
  Proof.
    induct fuel1.
    - simplify.
      contradiction.
    - intros v1 c v2 H.
      cases c; solve_monotone.
  Qed.

  Lemma run_monotone: forall fuel1 fuel2 v1 c v2,
      fuel1 <= fuel2 ->
      run fuel1 v1 c v2 ->
      run fuel2 v1 c v2.
  Proof.
    induct fuel2.
    - simplify.
      assert (fuel1 = 0) by linear_arithmetic.
      rewrite H1 in H0.
      simplify.
      assumption.
    - intros v1 c v2 H.
      assert (fuel1 = S fuel2 \/ fuel1 <= fuel2) by linear_arithmetic.
      destruct H0.
      + rewrite H0.
        trivial.
      + intro.
        apply run_monotone_helper.
        apply IHfuel2; assumption.
  Qed.

  (* For the other direction, we could naively start proving it like this: *)
  Theorem eval_to_run: forall v1 c v2,
      eval v1 c v2 -> exists fuel, run fuel v1 c v2.
  Proof.
    induct 1; simplify.
    (* This proof is relatively short and straightforward, but dealing with
       existentials is not very pleasant!

       This problem becomes worse if we make many proofs about "run".  So, instead,
       let's look at a nicer formulation of this theorem. *)
  Abort. (* <-- do not change this line *)


  (* We will first define a wrapper around "run" that hides the existential: *)
  Definition wrun (v1: valuation) (c: cmd) (v2: valuation): Prop :=
    exists fuel, run fuel v1 c v2.

  (* The idea is that in the run_to_eval proof above, using the constructors of
     "eval", i.e. doing "eapply EvalAssign", "eapply EvalSeq", "eapply EvalIfTrue",
     was quite convenient, so let's expose the same "API" for constructing proofs
     of "run" (or actually, proofs of the slightly nicer "wrun"). *)

  (* Now let's define proof rules to get the same "API" for "wrun" as for "eval".
     Hint: Again, some proof automation might simplify the task (but manual proofs are
     possible too, of course).  You may find the `max` function useful. *)

Ltac solve_wrun :=
  simplify; unfold wrun in *; propositional; match goal with
  | _ => exists 1; solve_wrun
  | |- _ \/ _ => apply or_introl; solve_wrun
  | |- _ \/ _ => apply or_intror; solve_wrun
  | H : exists _, _ |- _ => destruct H; solve_wrun
  | x : nat |- _ => exists x; solve_wrun
  | x : nat |- _ => exists (S x); solve_wrun
  | x : nat, y: nat |- _ => exists (S (max x y)); solve_wrun
  | x : valuation |- _ => exists x; solve_wrun
  | H : run ?fuel _ _ _ |- _ => apply run_monotone with (fuel1 := fuel); try linear_arithmetic; assumption
  | _ => equality
  | _ => assumption
  end.

  Definition WRunSkip_statement : Prop :=
    forall v,
      wrun v Skip v.
  Lemma WRunSkip: WRunSkip_statement.
  Proof.
    unfold WRunSkip_statement.
    solve_wrun.
  Qed.

  Definition WRunAssign_statement : Prop :=
    forall v x e a,
      interp e v a ->
      wrun v (Assign x e) (v $+ (x, a)).
  Lemma WRunAssign: WRunAssign_statement.
  Proof.
    unfold WRunAssign_statement.
    solve_wrun.
  Qed.

  Definition WRunSeq_statement : Prop :=
    forall v c1 v1 c2 v2,
      wrun v c1 v1 ->
      wrun v1 c2 v2 ->
      wrun v (Sequence c1 c2) v2.
  Lemma WRunSeq: WRunSeq_statement.
  Proof.
    unfold WRunSeq_statement.
    solve_wrun.
  Qed.

  (* For the next few lemmas, we've left you the job of stating the theorem as
     well as proving it. *)

  Definition WRunIfTrue_statement : Prop :=
    forall v c1 e c2 v2 r,
      interp e v r ->
      r <> 0 ->
      wrun v c1 v2 ->
      wrun v (If e c1 c2) v2.
  Lemma WRunIfTrue: WRunIfTrue_statement.
  Proof.
    unfold WRunIfTrue_statement.
    solve_wrun.
  Qed.

  Definition WRunIfFalse_statement : Prop :=
    forall v c1 e c2 v2,
      interp e v 0 ->
      wrun v c2 v2 ->
      wrun v (If e c1 c2) v2.
  Lemma WRunIfFalse: WRunIfFalse_statement.
  Proof.
    unfold WRunIfFalse_statement.
    solve_wrun.
  Qed.

  (* somehow solve_wrun enters an infinite loop for this one *)
  Definition WRunWhileTrue_statement : Prop :=
    forall v body e v1 v2 r,
      interp e v r ->
      r <> 0 ->
      wrun v body v1 ->
      wrun v1 (While e body) v2 ->
      wrun v (While e body) v2.
  Lemma WRunWhileTrue: WRunWhileTrue_statement.
  Proof.
    unfold WRunWhileTrue_statement.
    simplify.
    unfold wrun in *.
    destruct H1.
    destruct H2.
    exists (S (max x x0)).
    simplify.
    apply or_introl.
    exists v1.
    exists r.
    propositional.
    - apply run_monotone with (fuel1 := x).
      + linear_arithmetic.
      + assumption.
    - apply run_monotone with (fuel1 := x0).
      + linear_arithmetic.
      + assumption.
  Qed.

  Definition WRunWhileFalse_statement : Prop :=
    forall v body e v2,
      interp e v 0 ->
      v = v2 ->
      wrun v (While e body) v2.
  Lemma WRunWhileFalse: WRunWhileFalse_statement.
  Proof.
    unfold WRunWhileFalse_statement.
    solve_wrun.
  Qed.

  (* Now, thanks to these helper lemmas, proving the direction from eval to wrun
     becomes easy: *)
Ltac values_if_needed := try apply values_to_interp; try assumption; equality.

  Theorem eval_to_wrun: forall v1 c v2,
      eval v1 c v2 ->
      wrun v1 c v2.
  Proof.
    induct 1.
    - apply WRunSkip.
    - rewrite H0.
      apply WRunAssign.
      values_if_needed.
    - apply WRunSeq with (v1 := v'); assumption.
    - apply WRunIfTrue with (r := a); values_if_needed.
    - apply WRunIfFalse; values_if_needed.
    - unfold wrun in IHeval.
      destruct IHeval.
      pose (run_monotone_helper _ _ _ _ H2) as H3.
      simplify.
      destruct H3 as (vmid, (Hbody, Hrest)).
      apply WRunWhileTrue with (v1 := vmid) (r := a);
        try values_if_needed;
        unfold wrun;
        exists x;
        assumption.
    - apply WRunWhileFalse; values_if_needed.
  Qed.

  (* Remember when we said earlier that [induct 1] does induction on the proof
     of [eval], whereas [induct c] does induction on the program itself?  Try
     proving the above with [induct c] instead of [induct 1], skipping straight
     to the [While] cases.  Why isn't the theorem provable this way? *)

  (* The following definitions are needed because of a limitation of Coq
     (the kernel does not recognize that a parameter can be instantiated by an
     inductive type).
     Please do not remove them! *)
  Definition values_alias_for_grading := values.
  Definition eval_alias_for_grading := eval.

  (* You've reached the end of this pset, congratulations! *)

  (* ****** Everything below this line is optional ****** *)

  (* Many of the proofs above can be automated.  A good way to test your
     automation is to make small changes to the language.

     For example, you could add an [Unset: string -> cmd] constructor to the
     definition of [cmd]; the semantics of that command should be to remove a
     variable from the current valuation (use [v $- "x"] to remove ["x"] from
     [v]).

     In our solution, adding [Unset] and updating definitions and proofs
     accordingly takes just a few extra lines.  Try it in yours! *)

  (* Let's take the deterministic semantics we used in OperationalSemantics.v but
     prefix them with "d" to mark them as deterministic: *)

  Fixpoint dinterp (e: arith) (v: valuation): nat :=
    match e with
    | Const n => n
    | Var x =>
      match v $? x with
      | None => 0
      | Some n => n
      end
    | Plus e1 e2 => dinterp e1 v + dinterp e2 v
    end.

  Inductive deval: valuation -> cmd -> valuation -> Prop :=
  | DEvalSkip: forall v,
      deval v Skip v
  | DEvalAssign: forall v x e,
      deval v (Assign x e) (v $+ (x, dinterp e v))
  | DEvalSeq: forall v c1 v1 c2 v2,
      deval v c1 v1 ->
      deval v1 c2 v2 ->
      deval v (Sequence c1 c2) v2
  | DEvalIfTrue: forall v e thn els v',
      dinterp e v <> 0 ->
      deval v thn v' ->
      deval v (If e thn els) v'
  | DEvalIfFalse: forall v e thn els v',
      dinterp e v = 0 ->
      deval v els v' ->
      deval v (If e thn els) v'
  | DEvalWhileTrue: forall v e body v' v'',
      dinterp e v <> 0 ->
      deval v body v' ->
      deval v' (While e body) v'' ->
      deval v (While e body) v''
  | DEvalWhileFalse: forall v e body,
      dinterp e v = 0 ->
      deval v (While e body) v.

  (* Now let's prove that if a program evaluates to a valuation according to the
     deterministic semantics, it also evaluates to that valuation according to
     the nondeterministic semantics (the other direction does not hold, though). *)
  Theorem deval_to_eval: forall v1 v2 c,
      deval v1 c v2 ->
      eval v1 c v2.
  Proof.
  Admitted.

  (* In deterministic semantics, Fixpoints work a bit better, because they
     can return just one value, and let's use "option" to indicate whether
     we ran out of fuel: *)
  Fixpoint drun(fuel: nat) (v: valuation) (c: cmd): option valuation. Admitted.

  (* More open-ended exercise:
     Now we have six different definitions of semantics:

                          deterministic     nondeterministic

     Inductive            deval             eval

     Wrapped Fixpoint     dwrun             wrun

     Fixpoint             drun              run

     We have proved that all the nondeterministic semantics are equivalent among
     each other.
     If you want, you could also prove that all the deterministic semantics are
     equivalent among each other and experiment whether it's worth creating an
     "Inductive"-like API for "dwrun", or whether you're ok dealing with drun's
     existentials when proving deval_to_drun.
     Moreover, we have proved that "deval" implies "eval", so every definition in
     the left column of the above table implies every definition in the right
     column of the table.
     If you're curious to learn more about the trade-offs between Inductive Props
     and Fixpoints, you can try to prove some of these implications directly
     and see how much harder than "deval_to_eval" it is (we believe that
     "deval_to_eval" is the simplest one).
   *)

End Impl.

Module ImplCorrect : Pset5Sig.S := Impl.

(* Authors:
   Samuel Gruetter
   Cl\u00e9ment Pit-Claudel *)
