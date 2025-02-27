(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 11 *)

Require Import Frap Pset11.Pset11Sig.

(* Programmers who start programming with threads and locks soon realize that it
 * is tricky to avoid *deadlocks*, where thread #1 is waiting to take a lock
 * held by thread #2, and thread #2 is waiting to take a lock held by thread #3,
 * and... thread #N is waiting to take a lock held by thread #1.  That's a wait
 * cycle, and none of the threads will ever make progress.
 *
 * The most common wisdom about avoiding deadlocks is to impose a *total order*
 * on the locks.  A thread is only allowed to acquire a lock that is *less than*
 * all locks it currently holds.  In this pset, we formalize a simple static
 * analysis checking that the total-order rule is obeyed, and we prove that any
 * program accepted by the analysis avoids deadlock. *)

(* Please start by reading the definitions in Pset11Sig.v! *)

(* Before diving into the proof hacking, it might be helpful to write a short
   sample program (in Coq) where thread 1 acquires lock 1 and then lock 2,
   while thread 2 tries to acquire lock 2 and then lock 1, and explain (in
   English) how a deadlock can happen: *)

Example bad: prog := 
  (Bind (Lock 1) (fun _ => Bind (Lock 2) (fun _ => Bind (Unlock 1) (fun _ => Unlock 2)))) ::
  (Bind (Lock 2) (fun _ => Bind (Lock 1) (fun _ => Bind (Unlock 2) (fun _ => Unlock 1)))) ::
[].

(* FILL IN explanation here 
  if thread 1 locks 1 then thread 2 locks 2 then both threads will be stuck
*)



(* And now, explain why the total-order rule would reject your example by copy-pasting
   the one rule which rejects it from Pset11Sig.v and briefly describing how it would
   reject it: *)

(* FILL IN explanation here
| GcLock : forall l a,
    (forall a', a' \in l -> a' > a) <-- this part rejects thread 1
    (* ^-- Note that this premise enforces the total order on locks!
     *     That is, every lock already held must be greater than the new one. *)
    -> goodCitizen l (Lock a) (l \cup {a})
*)

(* The two questions above are not graded, but we hope they help you understand
   the material better! *)

(* Since we use the [a_useful_invariant] theorem, proving [deadlock_freedom]
   reduces to proving this lemma \u2014 the only one in this Pset!  See hints at the bottom
   of the signature file if you get stuck, and of course come to office hours if you 
   have any questions or need help. *)



Module Impl.

Lemma freedom_helper :
  forall (h : heap) (lall l l2 : locks) (c : cmd),
  goodCitizen l c l2 ->
  ~finished c ->
  l \subseteq lall ->
  (
    lall = {} \/
    (exists x, x \in l /\ forall x', (x' \in lall -> x <= x'))) ->
  exists h' lall' c', step0 (h, lall, c) (h', lall', c').
Proof.
  induct 1; simplify.
  - pose (Finished r).
    contradiction.
  - excluded_middle (finished c1).
    + invert H5.
      exists h.
      exists lall.
      exists (c2 r).
      apply StepBindProceed.
    + assert (exists (h' : heap) (lall' : locks) (c' : cmd),
                  step0 (h, lall, c1) (h', lall', c')).
      * apply IHgoodCitizen; assumption.
      * do 3 destruct H6.
        exists x.
        exists x0.
        exists (x <- x1; c2 x).
        apply StepBindRecur.
        assumption.
  - exists h.
    exists lall.
    exists (Return (h $! a)).
    apply StepRead.
  - exists (h $+ (a, v)).
    exists lall.
    exists (Return 0).
    apply StepWrite.
  - exists h.
    exists (lall \cup {a}).
    exists (Return 0).
    apply StepLock.
    propositional.
    + rewrite H4 in H3.
      contradiction.
    + destruct H4.
      propositional.
      pose (H5 a H3).
      pose (H x H4).
      linear_arithmetic.
  - exists h.
    exists (lall \setminus {a}).
    exists (Return 0).
    apply StepUnlock.
    apply subseteq_In with (s1 := l); assumption.
Qed.

Lemma goodCitizen_inside :
  forall p p1 l c p2,
  p = p1 ++ (l, c) :: p2 ->
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  goodCitizen l c {}.
Proof.
  simplify.
  rewrite H in H0.
  pose Forall_app_fwd.
  pose (Forall_app_fwd p1 ((l, c) :: p2) H0) as H1.
  destruct H1.
  pose (Forall_app_fwd [(l, c)] p2 H2) as H3.
  destruct H3.
  invert H3.
  simplify.
  assumption.
Qed.

Lemma inside_subset :
  forall p1 l c p2 p,
  p = p1 ++ (l, c) :: p2 ->
  l \subseteq (locksOf p).
Proof.
  induct p1; simplify; rewrite H; simplify.
  - sets.
  - assert (l \subseteq locksOf (p1 ++ (l, c) :: p2)).
    + apply IHp1 with (c) (p2).
      equality.
    + destruct a.
      sets.
Qed.

Lemma freedom_helper_2 : 
  forall (h : heap) (p : prog'),
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  (exists p1 l c p2,
    p = p1 ++ (l, c) :: p2 /\
    ~finished c /\
    (
      locksOf p = {} \/
      (exists x, x \in l /\ forall x', (x' \in locksOf p -> x <= x')))) ->
  exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p'.
Proof.
  simplify.
  do 5 destruct H0.
  assert (progOf p = progOf x ++ x1 :: progOf x2).
  - rewrite H0.
    apply progOf_app.
  - rewrite H2.
    assert (exists h' lall' c', step0 (h, locksOf p, x1) (h', lall', c')).
    + apply freedom_helper with (l := x0) (l2 := {}).
      * apply goodCitizen_inside with (p := p) (p1 := x) (p2 := x2); assumption.
      * propositional.
      * apply inside_subset with (p1 := x) (c := x1) (p2 := x2).
        assumption.
      * propositional.
    + do 3 destruct H3.
      exists (x3, x4, progOf x ++ x5 :: progOf x2).
      apply StepThread.
      assumption.
Qed.
Lemma nonempty_minimum_helper : forall l : locks,
  forall y,
    (forall x', x' \in l -> x' > y) \/ (exists x, x \in l /\ forall x', x' \in l -> x' >= x).
Proof.
  induct y.
  - assert (forall x', x' \in l -> x' >= 0) by linear_arithmetic.
    excluded_middle (0 \in l).
    + apply or_intror.
      exists 0.
      propositional.
    + apply or_introl.
      simplify.
      assert (x' <> 0) by sets.
      pose (H x' H1).
      linear_arithmetic.
  - propositional.
    excluded_middle (S y \in l).
    + apply or_intror.
      exists (S y).
      propositional.
    + apply or_introl.
      simplify.
      assert (x' <> S y) by sets.
      pose (H x' H1).
      linear_arithmetic.
Qed.

Lemma nonempty_minimum : forall l : locks,
  l <> {} -> exists x, x \in l /\ forall x', x' \in l -> x' >= x.
Proof.
  simplify.
  excluded_middle (exists x, x \in l).
  - destruct H0.
    pose (nonempty_minimum_helper l x).
    propositional.
    pose (H1 x H0).
    linear_arithmetic.
  - assert (l = {}).
    + sets.
      assert (exists x : nat, l x).
      * eauto.
      * contradiction.
    + contradiction.
Qed.

Lemma in_one_of_them :
  forall (p : prog') x,
  x \in locksOf p ->
  (exists p1 l c p2,
    p = p1 ++ (l, c) :: p2 /\
    x \in l).
Proof.
  induct p; simplify.
  - contradiction.
  - destruct a as (l, c).
    sets.
    + exists [].
      exists l.
      exists c.
      exists p.
      propositional.
    + pose (IHp x H0) as H.
      do 4 destruct H.
      exists ((l, c) :: x0).
      exists x1.
      exists x2.
      exists x3.
      propositional.
      simplify.
      equality.
Qed.

Lemma finished_or_not_finished :
  forall (p : prog'),
  Forall finished (progOf p) \/
  (exists p1 l c p2,
    p = p1 ++ (l, c) :: p2 /\
    ~finished c).
Proof.
  induct p; simplify.
  - auto.
  - destruct a as (l, c).
    excluded_middle (finished c).
    + propositional.
      * auto.
      * apply or_intror.
        do 4 destruct H0.
        exists ((l, c) :: x).
        exists x0.
        exists x1.
        exists x2.
        propositional.
        simplify.
        equality.
    + apply or_intror.
      exists [].
      exists l.
      exists c.
      exists p.
      propositional.
Qed.

(* HINT 1-5 (see Pset11Sig.v) *)   
Lemma deadlock_freedom' :
  forall (h : heap) (p : prog'),
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  Forall finished (progOf p) \/ (exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p').
Proof.
  simplify.
  excluded_middle (locksOf p = {}).
  - pose (finished_or_not_finished p).
    propositional.
    apply or_intror.
    apply freedom_helper_2; auto.
    do 4 destruct H1.
    exists x.
    exists x0.
    exists x1.
    exists x2.
    propositional.
  - apply or_intror.
    apply freedom_helper_2; auto.
    destruct (nonempty_minimum (locksOf p) H0).
    destruct H1.
    pose (in_one_of_them p x H1) as H3.
    do 4 destruct H3.
    exists x0.
    exists x1.
    exists x2.
    exists x3.
    propositional.
    + invert H3.
      assert (goodCitizen x1 (Return r) {}).
      * apply goodCitizen_inside with (p := x0 ++ (x1, Return r) :: x3) (p1 := x0) (p2 := x3); auto.
      * invert H3.
        contradiction.
    + apply or_intror.
      exists x.
      propositional.
Qed.

(* Here's how we can use [a_useful_invariant] to go from [deadlock_freedom'] to
   [deadlock_freedom]: *)
Theorem deadlock_freedom :
  forall h p,
    Forall (fun c => goodCitizen {} c {}) p ->
    invariantFor (trsys_of h {} p) (fun h_l_p =>
                                      let '(_, _, p') := h_l_p in
                                      Forall finished p'
                                      \/ exists h_l_p', step h_l_p h_l_p').
Proof.
  (* To begin with, we strengthen the invariant to the one proved in Pset11Sig. *)
  simplify.
  eapply invariant_weaken.
  eauto using a_useful_invariant.

  (* What's left is to prove that this invariant implies deadlock-freedom. *)
  first_order.
  destruct s as [[h' ls] p'].
  invert H0.

  (* We don't actually need to use the [disjointLocks] property.  It was only
   * important in strengthening the induction to prove that other invariant. *)
  clear H6.

  (* At this point, we apply the lemma that we expect you to prove! *)
  apply deadlock_freedom'. assumption.
Qed.
End Impl.

Module ImplCorrect : Pset11Sig.S := Impl.

(* Authors:
   Adam Chlipala,
   Peng Wang,
   Samuel Gruetter *)
