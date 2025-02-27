(*|
=============================================================
 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 8
=============================================================
|*)

Require Import Pset8.Pset8Sig.

(*|
Introduction
============

Computer programs commonly manipulate data from different sources, at different levels of privacy or trust.
An e-commerce website, for example, might keep track of the contents of each individual cart,
and it would be a severe issue if one user got access to the content of another user's cart.

Such \u201cinformation-flow\u201d issues are of a different nature from the functionality bugs that we usually think of,
but they are also pervasive and tricky to detect and fix:
for example, for a few weeks in 2011,
Facebook's abuse-reporting tool made it possible to access a user's private photos
by reporting one of their *public* photos for abuse:
the tool would then conveniently offer to report other photos,
*including private ones* that the reporter was not allowed to access.
(https://www.zdnet.com/article/facebook-flaw-allows-access-to-private-photos/)

In this pset, we will see how type systems can help with information-flow issues.
We will operate in a simplified setting in which all information is either \u201cpublic\u201d or \u201cprivate\u201d,
and we will concern ourselves only with *confidentiality*,
the property that private inputs should not influence public program outputs.

Informally, we'll prove the correctness of a type system such that type-safe programs do not leak private data:
that is, we'll prove that changing the private inputs of a well-typed program does not change its public outputs.
We'll say that well-typed programs are \u201cconfidential\u201d.

Note that this formulation doesn't rule out side channels:
changing the private inputs of a program might change its runtime or even whether it terminates.

Language definition
===================

This is as usual:
|*)

Module Impl.
Inductive bop := Plus | Minus | Times.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Bop (b : bop) (e1 e2 : arith).

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Declare Scope  arith_scope.
Notation "a + b" := (Bop Plus a b) : arith_scope.
Notation "a - b" := (Bop Minus a b) : arith_scope.
Notation "a * b" := (Bop Times a b) : arith_scope.
Delimit Scope arith_scope with arith.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (thn els : cmd)
| While (e : arith) (body : cmd).

(* Here are some notations for the language, which again we won't really
 * explain. *)
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' thn 'else' els 'done'" := (If e%arith thn els) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

(*|
Program semantics
=================

And the semantics of the language are as expected; the language is made deterministic by defaulting to 0 when a variable is undefined.
|*)

Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Bop bp e1 e2 =>
    match bp with
    | Plus => Nat.add
    | Minus => Nat.sub
    | Times => Nat.mul
    end (interp e1 v) (interp e2 v)
  end.

Inductive eval : valuation -> cmd -> valuation -> Prop :=
| EvalSkip : forall v,
    eval v Skip v
| EvalAssign : forall v x e,
    eval v (Assign x e) (v $+ (x, interp e v))
| EvalSeq : forall v c1 v1 c2 v2,
    eval v c1 v1
    -> eval v1 c2 v2
    -> eval v (Sequence c1 c2) v2
| EvalIfTrue : forall v e thn els v',
    interp e v <> 0
    -> eval v thn v'
    -> eval v (If e thn els) v'
| EvalIfFalse : forall v e thn els v',
    interp e v = 0
    -> eval v els v'
    -> eval v (If e thn els) v'
| EvalWhileTrue : forall v e body v' v'',
    interp e v <> 0
    -> eval v body v'
    -> eval v' (While e body) v''
    -> eval v (While e body) v''
| EvalWhileFalse : forall v e body,
    interp e v = 0
    -> eval v (While e body) v.

(*|
Typing judgment
===============

The `Confidential` judgment below indicates that a program respects confidentiality.
It takes a set of public variables and a command and returns a `Prop` indicating whether the program is safe.  Take the time to understand exactly how `Confidential` works (or, even better, take a few moments to think how you would define a `Confidential` predicate).

In full generality, an information-flow system associates a label to each variable.
We'll simplify things and classify variables as \u201cpublic\u201d or \u201cprivate\u201d,
and instead of having a map giving the label of each value,
we'll keep track of the set of all public variables.

First, we need a way to collect the variables of an expression
(we haven't seen the `set` type too often; see the tips in ``Pset8Sig.v`` for a quick recap).
|*)

Fixpoint vars (e: arith) : set var :=
  match e with
  | Const n => {} (** A constant has no variables **)
  | Var x => {x} (** A variable has\u2026 one variable! **)
  | Bop _ e1 e2 => vars e1 \cup vars e2 (** An operator's variables are the variables of its subterms **)
  end.

(*|
The parameter `pub` below represents the set of all public variables.
This is predeclared and fixed.
But there is also a distinct `set var` argument.
This is because we need to consider *implicit* as well as *explicit* flows.

- An explicit flow happens when assigning to a variable.
  If `e` mentions variable `x`, then `y := e` may cause data to flow from `x` into `y`.
  If `x` is private and `y` is public, we want to rule that out.

- An implicit flow happens when assigning to a variable *under a conditional*.
  If `e` mentions variable `x`, then `when e then y := 1` may cause data to flow from `x` to `y`
  (can you see why?).  There, too, if `x` is private and `y` is public, we want to disallow this flow.

This is why we have the second `set var` (`cv`) argument below:
in addition to the set of public variables, =
we keep track of the set of variables from which data may flow implicitly via their effect on control flow.
We call that set \u201ccv\u201d, for \u201ccontrol variables\u201d.
|*)

Inductive Confidential (pub: set var) : set var (* cv *) -> cmd (* program *) -> Prop :=
| ConfidentialSkip : forall cv,
    Confidential pub cv Skip
(** A `Skip` is safe. **)
| ConfidentialAssignPrivate : forall cv x e,
    ~ x \in pub ->
    Confidential pub cv (Assign x e)
(** Assigning to a private variable is safe. **)
| ConfidentialAssignPublic : forall cv x e,
    vars e \subseteq pub ->
    cv \subseteq pub ->
    Confidential pub cv (Assign x e)
(** Assigning to a public variable variable is safe as long as the expression does not mention private variables and we are not under a conditional that depends on private variables. **)
| ConfidentialSeq : forall cv c1 c2,
    Confidential pub cv c1 ->
    Confidential pub cv c2 ->
    Confidential pub cv (Sequence c1 c2)
(** A sequence is safe if both halves of it are safe. **)
| ConfidentialIf : forall cv e thn els,
    Confidential pub (cv \cup vars e) thn ->
    Confidential pub (cv \cup vars e) els ->
    Confidential pub cv (If e thn els)
(** A conditional is safe if both branches are safe, noting that the branches run with additional variables in the `cv`. **)
| ConfidentialWhile : forall cv e body,
    Confidential pub (cv \cup vars e) body ->
    Confidential pub cv (While e body).
(** A while loop is safe if its body is safe, noting that the body runs with additional variables in the `cv`. **)

(*|
Here are a few examples:
|*)

Definition pub_example := {"x", "y", "z"}. (* Variables x, y, z are public. *)

Example confidential_prog :=
  ("x" <- "y" + 1;;
   "a" <- "a" * "b";;
   when "y" then "a" <- 0 else "b" <- 0 done).

Goal Confidential pub_example {} confidential_prog.
Proof.
  unfold confidential_prog, pub_example.
  apply ConfidentialSeq; simplify.
  - apply ConfidentialSeq; simplify.
    + apply ConfidentialAssignPublic; simplify.
      * sets.
      * sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
  - apply ConfidentialIf; simplify.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
Qed.

Example leaky_prog :=
  (when "a" then "x" <- 1 else "x" <- 2 done).

Goal ~ Confidential pub_example {} leaky_prog.
Proof.
  unfold leaky_prog, pub_example, not; simplify.
  invert H; simplify.
  invert H3; simplify.
  - sets.
  - pose proof @subseteq_In _ "a" _ _ H4.
    sets.
Qed.

(*|
Proof of noninterference
=========================

We first need a relation to characterize \u201cequivalent\u201d valuations
\u2014 that is, valuations that agree on all public variables.
`restrict s m` means restrict the valuation `m` to just the keys in `s`:
|*)

Definition same_public_state pub (v1 v2: valuation) :=
  restrict pub v1 = restrict pub v2.

(* Before we get started proving properties of our type system, please read
   Pset8Sig.v and consider the questions below. The only graded question is
   the multiple-choice one,  but we are assigning the rest in hopes that they
   help you complete the following parts.

 Suppose an expression contains only public variables. Under what valuations 
 do we expect them to evaluate to the same value?



 Suppose an expression evaluates to different values under different
 valuations. What do we know about this expression if the different valuations
 share the same public state? Do we know anything if the valuations do not 
 share the same public state?



 The noninterference property says that running a program in states with 
 private variables holding potentially different values does not change the 
 public outputs of the program.

 The key difficulty is to deal with *divergence* \u2014 the cases where the two 
 program executions take different paths.

 When does this happen?  How does that translate in terms of the variables
 in `cv`?
  
 Can a divergent execution affect the values of public variables?



 When a Confidential program executes, in what ways can it modify the 
 valuation? How does this depend on the values of `cv`?


 Finally, can the value of a private variable (one not in `pub`) determine
 whether a confidential program terminates? Assign the definition below to
 `true` if so, and `false` if not.

 *)

Definition private_can_determine_termination : bool := true.

Lemma restrict_add_yes : forall (v : valuation) x y (P : var -> Prop), P x ->
  restrict P (v $+ (x, y)) = (restrict P v) $+ (x, y).
Proof.
  simplify.
  apply fmap_ext.
  intro k.
  cases (k ==v x).
  - transitivity (Some y).
    + rewrite lookup_restrict_true.
      * simplify.
        equality.
      * rewrite e.
        assumption.
    + simplify.
      equality.
  - excluded_middle (P k).
    + transitivity (v $? k).
      * rewrite lookup_restrict_true.
        -- simplify.
           equality.
        -- assumption.
      * rewrite lookup_add_ne; auto.
        rewrite lookup_restrict_true; auto.
    + transitivity (None : option nat).
      * apply lookup_restrict_false.
        assumption.
      * rewrite lookup_add_ne; auto.
        rewrite lookup_restrict_false; auto.
Qed.

Lemma restrict_add_no : forall (v : valuation) x y (P : var -> Prop), ~ P x ->
  restrict P (v $+ (x, y)) = restrict P v.
Proof.
  simplify.
  apply fmap_ext.
  intro k.
  cases (k ==v x).
  - transitivity (None : option nat).
    + apply lookup_restrict_false.
      rewrite e.
      assumption.
    + symmetry.
      apply lookup_restrict_false.
      rewrite e.
      assumption.
  - excluded_middle (P k).
    + transitivity (v $? k).
      * transitivity ((v $+ (x, y) $? k)).
        -- apply lookup_restrict_true.
           assumption.
        -- simplify.
           equality.
      * rewrite lookup_restrict_true; auto.
    + transitivity (None : option nat).
      * apply lookup_restrict_false.
        assumption.
      * symmetry.
        apply lookup_restrict_false.
        assumption.
Qed.

Lemma restrict_interp : forall v e pub,
  vars e \subseteq pub -> interp e v = interp e (restrict pub v).
Proof.
  induct e; simplify.
  - equality.
  - sets.
    pose (H x).
    propositional.
    rewrite lookup_restrict_true; auto.
  - sets.
    rewrite IHe1 with (pub).
    + rewrite IHe2 with (pub); auto.
    + auto.
Qed.

Lemma interp_same : forall v1 v2 e pub,
  vars e \subseteq pub ->
  restrict pub v1 = restrict pub v2 ->
  interp e v1 = interp e v2.
Proof.
  simplify.
  rewrite restrict_interp with (pub := pub); auto.
  rewrite restrict_interp with (pub := pub) (v := v2); auto.
  equality.
Qed.

Lemma confidential_subset : forall pub cv1 cmd,
  Confidential pub cv1 cmd ->
  forall cv2,
  cv2 \subseteq cv1 ->
  Confidential pub cv2 cmd.
Proof.
  induct 1; simplify.
  - apply ConfidentialSkip.
  - apply ConfidentialAssignPrivate.
    assumption.
  - apply ConfidentialAssignPublic.
    + assumption.
    + sets.
  - apply ConfidentialSeq; auto.
  - apply ConfidentialIf.
    + apply IHConfidential1.
      sets.
    + apply IHConfidential2.
      sets.
  - apply ConfidentialWhile.
    apply IHConfidential.
    sets.
Qed.

Lemma no_effect : forall v c v',
  eval v c v' ->
  forall pub cv,
  Confidential pub cv c ->
  ~ cv \subseteq pub ->
  restrict pub v' = restrict pub v.
Proof.
  induct 1; intros pub cv Hconf Hns; invert Hconf.
  - equality.
  - apply restrict_add_no.
    assumption.
  - apply restrict_add_no.
    contradiction.
  - transitivity (restrict pub v1).
    + apply IHeval2 with (cv); assumption.
    + apply IHeval1 with (cv); assumption.
  - apply IHeval with (cv := cv \cup vars e).
    + assumption.
    + sets.
  - apply IHeval with (cv := cv \cup vars e).
    + assumption.
    + sets.
  - transitivity (restrict pub v').
    + apply IHeval2 with (cv).
      * apply ConfidentialWhile.
        assumption.
      * assumption.
    + apply IHeval1 with (cv := cv \cup vars e).
      * assumption.
      * sets.
  - equality.
Qed.

Lemma no_effect_while : forall e c v v' pub,
  eval v (while e loop c done) v' ->
  ~ vars e \subseteq pub ->
  Confidential pub ({} \cup vars e) c ->
  restrict pub v' = restrict pub v.
Proof.
  induct 1; intros Hns Hconf.
  - rewrite IHeval2.
    + apply no_effect with (c := c) (cv := {} \cup vars e).
      * assumption.
      * assumption.
      * sets.
    + assumption.
    + assumption.
  - equality.
Qed.

Theorem non_interference_helper :
  forall pub c v1 v1',
    eval v1 c v1' ->
  forall v2 v2',
    eval v2 c v2' ->
    Confidential pub {} c ->
    same_public_state pub v1 v2 ->
    same_public_state pub v1' v2'.
Proof.
  induct 1;
    intros w w2 Heval2 Hconf Hsame;
    invert Heval2;
    invert Hconf.
  - assumption.
  - unfold same_public_state.
    rewrite restrict_add_no; auto.
    rewrite restrict_add_no; auto.
  - unfold same_public_state.
    excluded_middle (pub x).
    + rewrite restrict_add_yes; auto.
      rewrite restrict_add_yes; auto.
      assert (interp e v = interp e w).
      * apply interp_same with (pub); assumption.
      * equality.
    + rewrite restrict_add_no; auto.
      rewrite restrict_add_no; auto.
  - apply IHeval2 with (v2 := v3); auto.
    apply IHeval1 with (v2 := w); auto.
  - apply IHeval with (v2 := w); auto.
    apply confidential_subset with (cv1 := {} \cup vars e).
    + assumption.
    + sets.
  - assert (~ vars e \subseteq pub).
    + intro.
      assert (interp e v = interp e w).
      * apply interp_same with (pub); assumption.
      * equality.
    + unfold same_public_state.
      rewrite no_effect with (v := v) (c := thn) (cv := {} \cup vars e); auto.
      * rewrite no_effect with (v := w) (c := els) (v' := w2) (cv := {} \cup vars e); auto.
        sets.
      * sets.
  - assert (~ vars e \subseteq pub).
    + intro.
      assert (interp e v = interp e w).
      * apply interp_same with (pub); assumption.
      * equality.
    + unfold same_public_state.
      rewrite no_effect with (v := v) (c := els) (cv := {} \cup vars e); auto.
      * rewrite no_effect with (v := w) (c := thn) (v' := w2) (cv := {} \cup vars e); auto.
        sets.
      * sets.
  - apply IHeval with (v2 := w); auto.
    apply confidential_subset with (cv1 := {} \cup vars e).
    + assumption.
    + sets.
  - apply IHeval2 with (v2 := v'0).
    + assumption.
    + apply ConfidentialWhile.
      assumption.
    + apply IHeval1 with (v2 := w); auto.
      apply confidential_subset with (cv1 := {} \cup vars e).
      * assumption.
      * sets.
  - assert (~ vars e \subseteq pub).
    + intro.
      assert (interp e v = interp e w2).
      * apply interp_same with (pub); assumption.
      * equality.
    + unfold same_public_state.
      rewrite no_effect_while with (e := e) (c := body) (v := v'); auto.
      rewrite no_effect with (v := v) (c := body) (cv := {} \cup vars e); auto.
      sets.
  - assert (~ vars e \subseteq pub).
    + intro.
      assert (interp e v = interp e w).
      * apply interp_same with (pub); assumption.
      * equality.
    + unfold same_public_state.
      rewrite no_effect_while with (e := e) (c := body) (v := v') (v' := w2); auto.
      rewrite no_effect with (v := w) (c := body) (cv := {} \cup vars e) (v' := v'); auto.
      sets.
  - assumption.
Qed.


(* HINT 1-2 (see Pset8Sig.v) *) 
Theorem non_interference :
  forall pub c v1 v1' v2 v2',
    eval v1 c v1' ->
    eval v2 c v2' ->
    Confidential pub {} c ->
    same_public_state pub v1 v2 ->
    same_public_state pub v1' v2'.
Proof.
  simplify.
  apply non_interference_helper with (c) (v1) (v2); assumption.
Qed.

(*|
Congratulations, you have proved that our type system is *sound*: it catches all leaky programs!
But it is not *complete*: there are some good programs that it rejects, too.
In other words, it *overapproximates* the set of unsafe programs.

Can you give an example of a safe program (a program that does not leak data) that our system would reject?
|*)

Definition tricky_example : cmd := "x" <- "w" + 1 - "w".

Lemma tricky_rejected : ~ Confidential pub_example {} tricky_example.
Proof.
  intro.
  invert H.
  - apply H2.
    unfold pub_example.
    sets.
  - simplify.
    assert (~ {"w"} \subseteq pub_example).
    + unfold pub_example.
      sets.
      pose (H "w").
      propositional; auto; equality.
    + contradiction.
Qed.

Lemma tc_helper : forall v1 v2 n n0,
  same_public_state pub_example v1 v2 ->
  same_public_state pub_example (v1 $+ ("x", n + 1 - n)) (v2 $+ ("x", n0 + 1 - n0)).
Proof.
  simplify.
  assert (n + 1 - n = 1) by linear_arithmetic.
  rewrite H0.
  assert (n0 + 1 - n0 = 1) by linear_arithmetic.
  rewrite H1.
  unfold same_public_state.
  rewrite restrict_add_yes.
  + rewrite restrict_add_yes.
    * equality.
    * unfold pub_example.
      sets.
  + unfold pub_example.
    sets.
Qed.

Lemma tricky_confidential :
  forall v1 v1' v2 v2',
    eval v1 tricky_example v1' ->
    eval v2 tricky_example v2' ->
    same_public_state pub_example v1 v2 ->
    same_public_state pub_example v1' v2'.
Proof.
  simplify.
  unfold tricky_example in *.
  invert H.
  invert H0.
  simplify.
  cases (v1 $? "w"); cases (v2 $? "w"); apply tc_helper; assumption.
Qed.
End Impl.

Module ImplCorrect : Pset8Sig.S := Impl.

(* Authors:
   Cl\u00e9ment Pit-Claudel
   Dustin Jamner
 *)
