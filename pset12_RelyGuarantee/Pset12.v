(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 12 *)

Require Import Frap Pset12.Pset12Sig.

Module Impl.
(* Part 1: read Pset12Sig.v and answer the questions below. This task is
 * ungraded, but we are assigning it in hope it helps you complete the
 * following parts.

(these are duplicative with past psets:)

- Which syntactic construct can be used to implement sequencing of two commands?

- Which step rules allow a sequenced program to make progress?

- Which step rule is used when a loop terminates?

- Which step rule is used when a loop continues?

- Why is there no step rule for Fail?

(these are about the programming language in this pset:)

- Which syntactic construct is used to spawn new threads?

- Which step rules allow a multi-threaded program to make progress?

- How can threads in this language communicate with each other?

- What do the steps that are factored out into the astep inductive have in common?

(these are about the program logic:)

- Which rule of the program logic handles astep commands?

- What is the meaning of the "rely" argument [R]?

- What would [R] be for a program that can run in any environment?

- What would [R] be for a program that can only run alone?

- Which constructors of [hoare_triple] change [R]? Do they make it more or less permissive?

- What is the meaning of the "guarantee" argument [G]?

- Which cases of [hoare_triple] require you to prove [G]?

- What would [G] be for a program that can run in any environment?

- What would [G] be for a program that can only run alone?

(these are about program logic tactics:)

- What syntactic forms of commands does [step] handle?

- What syntactic forms of commands does [fork] handle?

- What are the six arguments to the tactic [fork]? Classify them into two groups of three, and then (differently) classify them into three pairs.

- What syntactic forms of commands does [atomic] handle?

- What is the argument to the tactic [atomic]?
*)

(* Part 2: prove a program correct *)

(* Pset12Example.v contains an example verification of a non-trivial program.
 * You can use it as a reference when trying to figure out what the rules,
 * lemmas, and tactics here do, but you are not required to understand it.
 * The program in this file is much simpler. *)

(* This lemma already exists! Find the original name and use it here to finish
   the definition. Why are we having you do this? This lemma is important to
   your solution, so we don't want you to forget it.
 *)  
Definition always_stableP_find_me : forall (t : Set) P R c G (Q : t -> _),
    hoare_triple P R c G Q -> stableP P R.
Proof.
  exact always_stableP.
Qed.

(*Lemma hti1 : forall init, hoare_triple (fun h : heap => h $! 0 >= init) (fun h h' : heap => False \/ h' $! 0 >= h $! 0)
  (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1))) (fun h h' : heap => h' $! 0 >= h $! 0)
  (fun (_ : unit) (h : heap) => h $! 0 > init).
Proof.
  simp.
  step.
  atomic (fun x (h : heap) => x >= init).
  simp.
  apply HtAtomic with (Q := (fun (_ : unit) (h : heap) => h $! 0 > init)).
  simp.
  atomic (fun (_ : unit) (h : heap) => h $! 0 > init).
  apply HtConsequence wit
  eapply HtConsequence with
    (P := fun _ : heap => r >= init)
    (R := fun h h' : heap => False \/ h' $! 0 >= h $! 0)
    (G := fun h h' : heap => h' $! 0 >= h $! 0).
  
  step.*)

(*Lemma hti1 : forall init, hoare_triple (fun h : heap => h $! 0 >= init) (fun _ h' : heap => False \/ h' $! 0 >= init)
  (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1))) (fun _ h' : heap => h' $! 0 >= init)
  (fun (_ : unit) (h : heap) => h $! 0 > init).
Proof.
  simp.
  step.
  atomic (fun x (h : heap) => x >= init).
  simp.
  apply HtAtomic with (Q := (fun (_ : unit) (h : heap) => h $! 0 > init)).
  simp.
  simp.
  simp.
  atomic (fun (_ : unit) (h : heap) => h $! 0 > init).*)
  
  

Lemma hti1 : forall init, hoare_triple (fun h : heap => h $! 0 >= init)
  (fun h h' : heap => False \/ h' $! 0 > init \/ h' $! 0 >= h $! 0)
  (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
  (fun h h' : heap => h' $! 0 > init \/ h' $! 0 >= h $! 0)
  (fun (_ : unit) (h : heap) => h $! 0 > init).
Proof.
  simp.
  step.
  atomic (fun x (h : heap) => x >= init).
  simp.
  atomic (fun (_ : unit) (h : heap) => h $! 0 > init).
Qed.

(* Verify that this program manages to increase the counter value. *)
Lemma ht_increment : forall init,
  hoare_triple
    (fun h => h $! 0 = init)
    (fun _ _ => False)
    (   (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
     || (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
    )
    (fun _ _ => True)
    (fun _ h => h $! 0 > init).
Proof.
  simp.
  fork (fun h => h $! 0 >= init)
       (fun (h : heap) h' => h' $! 0 > init \/ h' $! 0 >= h $! 0)
       (fun (_ : unit) h => h $! 0 > init)
       (fun h => h $! 0 >= init)
       (fun (h : heap) h' => h' $! 0 > init \/ h' $! 0 >= h $! 0)
       (fun (_ : unit) h => h $! 0 > init).
  apply hti1.
  apply hti1.
  simp.
  simp.
  simp.
  simp.
  simp.
Qed.

(* Part 3: prove soundness of the program logic *)

(* Now it remains to prove that having a [hoare_triple] actually means
 * that execution will proceed safely, and if the program terminates then the
 * postcondition will be satisfied. *)

(* If non-negligible time has passed since you read the sig file, please
 * review the definitions of [trsys_of] and [notAboutToFail] now. *)

(* Then, feel free to just skim the next lemmas, right until the final
 * theorem you are asked to prove. *)

(* Here are a few more lemmas that you may find helpful: *)

Lemma HtStrengthen : forall {t : Set} P R c G (Q : t -> _) (P' : hprop),
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> stableP P' R
    -> hoare_triple P' R c G Q.
Proof. eauto. Qed.

Lemma HtWeakenFancy : forall {t : Set} P R c G Q (G' : hrel) (Q' : t -> hprop),
    hoare_triple P R c G Q
    -> (forall v h, Q v h -> Q' v h)
    -> (forall h h', G h h' -> G' h h')
    -> hoare_triple P R c G' Q'.
Proof. eauto using always_stableP. Qed.

Lemma HtReturn' : forall {t : Set} (P : hprop) (R G : hrel) (Q : _ -> hprop) (v : t),
    stableP P R
    -> (forall h, P h -> Q v h)
    -> hoare_triple P R (Return v) G Q.
Proof.
  simplify.
  eapply HtConsequence with (P' := P) (R' := R) (G' := G); eauto.
  simplify; propositional; subst; eauto.
Qed.

Lemma stableP_self : forall h R, stableP (fun h' => R^* h h') R.
Proof. simp. eauto using trc_trans. Qed.

Lemma stableP_star : forall R h h', R^* h h' ->
    forall P, stableP P R -> P h -> P h'.
Proof. induct 1; simplify; eauto. eapply IHtrc; eauto. Qed.

Lemma stableP_weakenR : forall P R, stableP P R -> forall R' : hrel,
    (forall h1 h2, R' h1 h2 -> R h1 h2) -> stableP P R'.
Proof. simp; eauto. Qed.

Local Hint Resolve stableP_self : core.

Lemma stable_stableQ : forall (t : Set) P (Q : t -> _) R r,
  stable P Q R -> stableP (Q r) R.
Proof. unfold stable; propositional; eauto. Qed.
Local Hint Resolve stable_stableQ : core.

Lemma stable_stableP : forall (t : Set) P (Q : t -> _) R,
  stable P Q R -> stableP P R.
Proof. unfold stable; propositional; eauto. Qed.
Local Hint Resolve stable_stableP : core.

Lemma trc_imply :forall t R (s s' : t), R^* s s' ->
  forall (R':_->_->Prop), (forall s s', R s s' -> R' s s') ->
  R'^* s s'.
Proof. induct 1; simplify; eauto. Qed.

Local Hint Extern 1 (_ >= _) => linear_arithmetic : core.
Local Hint Constructors notAboutToFail : core.

Lemma hoare_triple_return : forall (t : Set) (P : hprop) R (r : t) G (Q : t -> hprop),
  hoare_triple P R (Return r) G Q ->
  forall h, P h -> Q r h.
Proof.
  induct 1; simp.
  apply H1.
  apply IHhoare_triple.
  apply H0.
  assumption.
Qed.

Lemma stable_and : forall (P1 P2 : hprop) R,
  stableP P1 R ->
  stableP P2 R ->
  stableP (fun h => P1 h /\ P2 h) R.
Proof.
  simp.
  eauto.
  eauto.
Qed.

Theorem guarantee_step : forall (t : Set) (P : hprop) R h c G Q,
  hoare_triple P R c G Q ->
  P h ->
  forall h' (c' : cmd t),
  step (h, c) (h', c') ->
  G^* h h'.
Proof.
  induct 1; simp.
  - invert H3; simp.
    + eapply H4.
      exact H7.
    + eauto.
  - invert H5.
    + eapply trc_imply.
      * eapply IHhoare_triple1.
        -- auto.
        -- exact H8.
      * propositional.
    + eapply trc_imply.
      * eapply IHhoare_triple2.
        -- auto.
        -- exact H8.
      * propositional.
  - invert H1.
  - invert H3.
    simp.
    + eauto.
    + eapply TrcFront.
      * apply (H tt); auto.
      * eauto.
  - invert H3.
    eauto.
  - eapply trc_imply.
    + eapply IHhoare_triple.
      * auto.
      * exact H6.
    + exact H3.
Qed.

Theorem hoare_triple_step : forall (t : Set) (P : hprop) R h c G Q,
  hoare_triple P R c G Q ->
  P h ->
  forall h' (c' : cmd t),
  step (h, c) (h', c') ->
  exists P', (hoare_triple P' R c' G Q /\ P' h').
Proof.
  induct 1; simp.
  - invert H3; simp.
    + destruct (H4 h' c1' H7) as (P', H3).
      exists P'.
      propositional.
      eapply HtBind.
      exact H5.
      exact H0.
    + exists (Q1 v0).
      propositional.
      * apply H0.
      * eapply hoare_triple_return; eauto.
  - invert H5; simp.
    + assert (exists (P' : hprop), hoare_triple P' (fun h h'0 : heap => R h h'0 \/ G2 h h'0) c1' G1 Q1 /\ P' h').
      * apply IHhoare_triple1.
        -- auto.
        -- assumption.
      * destruct H5 as (P', H5).
        exists (fun h => P' h /\ P2 h).
        propositional.
        -- eapply HtPar.
           ++ exact H6.
           ++ exact H0.
           ++ apply stable_and.
              ** apply stableP_weakenR with (R := fun h h' : heap => R h h' \/ G2 h h').
                 --- eapply always_stableP_find_me.
                     exact H6.
                 --- propositional.
              ** apply stableP_weakenR with (R := fun h h' : heap => R h h' \/ G1 h h').
                 --- eapply always_stableP_find_me.
                     exact H0.
                 --- propositional.
           ++ equality.
           ++ propositional.
        -- eapply stableP_star.
           ++ eapply guarantee_step with (G := G1) (h := h) (h' := h').
              ** exact H.
              ** auto.
              ** exact H8.
           ++ apply stableP_weakenR with (R := fun h h' : heap => R h h' \/ G1 h h').
              ** eapply always_stableP_find_me.
                 exact H0.
              ** propositional.
           ++ auto.
    + assert (exists (P' : hprop), hoare_triple P' (fun h h'0 : heap => R h h'0 \/ G1 h h'0) c2' G2 Q2 /\ P' h').
      * apply IHhoare_triple2.
        -- auto.
        -- assumption.
      * destruct H5 as (P', H5).
        exists (fun h => P' h /\ P1 h).
        propositional.
        -- eapply HtPar.
           ++ exact H.
           ++ exact H6.
           ++ apply stable_and.
              ** apply stableP_weakenR with (R := fun h h' : heap => R h h' \/ G1 h h').
                 --- eapply always_stableP_find_me.
                     exact H6.
                 --- propositional.
              ** apply stableP_weakenR with (R := fun h h' : heap => R h h' \/ G2 h h').
                 --- eapply always_stableP_find_me.
                     exact H.
                 --- propositional.
           ++ equality.
           ++ propositional.
        -- eapply stableP_star.
           ++ eapply guarantee_step with (G := G2) (h := h) (h' := h').
              ** exact H0.
              ** auto.
              ** exact H8.
           ++ apply stableP_weakenR with (R := fun h h' : heap => R h h' \/ G2 h h').
              ** eapply always_stableP_find_me.
                 exact H.
              ** propositional.
           ++ auto.
  - invert H1.
  - invert H3.
    simp.
    + exists (Q (h' $! a1)).
      propositional.
      * eapply HtConsequence.
        -- apply HtReturn.
           eapply stable_stableQ.
           exact H1.
        -- simp.
           exact H3.
        -- simp.
        -- propositional.
        -- simp.
           exact H3.
        -- eapply stable_stableQ.
           exact H1.
      * eapply H0.
        -- exact H2.
        -- eauto.
    + exists (Q tt).
      propositional.
      * eapply HtConsequence.
        -- apply HtReturn.
           eapply stable_stableQ.
           exact H1.
        -- simp.
           exact H3.
        -- simp.
        -- propositional.
        -- simp.
           exact H3.
        -- eapply stable_stableQ.
           exact H1.
      * eapply H0.
        -- exact H2.
        -- eauto.
  - invert H3.
    simp.
    exists (I (Again init)).
    propositional.
    step.
    + apply H.
    + cases r.
      * eapply HtConsequence.
        -- apply HtReturn.
           apply H1.
        -- simp.
           exact H3.
        -- simp.
        -- propositional.
        -- simp.
           exact H3.
        -- apply H1.
      * apply HtLoop; assumption.
  - destruct (IHhoare_triple (H0 h H5) h' c' H6) as (P'', H7).
    exists P''.
    propositional.
    eapply HtConsequence.
    + exact H8.
    + propositional.
    + auto.
    + auto.
    + auto.
    + eapply stableP_weakenR.
      * eapply always_stableP_find_me.
        exact H8.
      * auto.
Qed.

Lemma hoare_triple_natf : forall (t : Set) (P : hprop) R h (c : cmd t) G Q,
  hoare_triple P R c G Q ->
  P h ->
  notAboutToFail c.
Proof.
  induct 1; simp.
  - eauto.
  - eauto 25.
  - eauto.
  - eauto.
  - eauto.
  - eauto.
Qed.

(* HINT 1-6 (see Pset12Sig.v) *)   
Theorem hoare_triple_sound : forall (t : Set) P (c : cmd t) Q,
  hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q ->
  forall h, P h ->
  invariantFor (trsys_of h c) (fun st => notAboutToFail (snd st)).
Proof.
  simp.
  apply invariant_weaken with (invariant1 := fun (st : (heap * cmd t)) =>
    let (h, c) := st in exists P, hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q /\ P h).
  - apply invariant_induction; simp.
    + eauto.
    + destruct s as (h0, c0).
      destruct s' as (h1, c1).
      destruct H1 as (P', H1).
      destruct H1.
      eapply hoare_triple_step.
      * eauto.
      * exact H3.
      * assumption.
  - destruct s.
    simp.
    eapply hoare_triple_natf.
    + exact H1.
    + exact H3.
Qed.

End Impl.

Module ImplCorrect : Pset12Sig.S := Impl.
