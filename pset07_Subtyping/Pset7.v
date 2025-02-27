(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 7 *)

Require Import Frap.Frap.
Require Import Pset7.Pset7Sig.

(* The following line forces you to use bullets or braces.  Remove it if you get
   errors like "Expected a single focused goal but 2 goals are focused." and you
   don't want to structure your proofs. *)
Set Default Goal Selector "!".
Set Implicit Arguments.

Module Impl.
(** * Subtyping *)

(* We can't resist fitting in another crucial aspect of type systems:
 * *subtyping*, which formalizes when any value of one type should also be
 * permitted as a value of some other type.  Languages like Java include
 * *nominal* subtyping, based on declared type hierarchies.  Instead, here we
 * will prove soundness of *structural* subtyping, whose rules we'll get to
 * shortly.  The simply typed lambda calculus will be our starting point. *)

(* Expression syntax *)
Inductive exp  :=
(* Our old friends from simply typed lambda calculus *)
| Var (x : var)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp)

(* New features, surrounding *tuple* types, which build composite types out of
 * constituents *)
| TupleNil
(* Empty tuple (no fields *)
| TupleCons (e1 e2 : exp)
(* Nonempty tuple, where [e1] is the first field of the tuple, and [e2] is a
 * nested tuple with all the remaining fields *)

| Proj (e : exp) (n : nat)
(* Grab the [n]th field of tuple [e]. *)
.

(* Values (final results of evaluation) *)
Inductive value : exp -> Prop :=
| VAbs : forall x e1, value (Abs x e1)
| VTupleNil : value TupleNil
| VTupleCons : forall e1 e2, value e1 -> value e2 -> value (TupleCons e1 e2)
.

(* The next few definitions are quite routine and should be safe to skim through
 * quickly; but start paying more attention when we get to defining the
 * subtyping relation! *)

(* Substitution (not capture-avoiding, for the usual reason) *)
Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
  match e2 with
  | Var y => if y ==v x then e1 else Var y
  | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
  | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  | TupleNil => TupleNil
  | TupleCons e2' e2'' => TupleCons (subst e1 x e2') (subst e1 x e2'')
  | Proj e2' n => Proj (subst e1 x e2') n
  end.

(* Evaluation contexts *)
Inductive context :=
| Hole
| App1 (C : context) (e2 : exp)
| App2 (v1 : exp) (C : context)
| TupleCons1 (C : context) (e2 : exp)
| TupleCons2 (v1 : exp) (C : context)
| Proj1 (C : context) (n : nat)
.

(* Plugging an expression into a context *)
Inductive plug : context -> exp -> exp -> Prop :=
| PlugHole : forall e, plug Hole e e
| PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
| PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')
| PlugTupleCons1 : forall C e e' e2,
    plug C e e'
    -> plug (TupleCons1 C e2) e (TupleCons e' e2)
| PlugTupleCons2 : forall v1 C e e',
    value v1
    -> plug C e e'
    -> plug (TupleCons2 v1 C) e (TupleCons v1 e')
| PlugProj : forall C e e' n,
    plug C e e'
    -> plug (Proj1 C n) e (Proj e' n)
.

(* Small-step, call-by-value evaluation *)
Inductive step0 : exp -> exp -> Prop :=
| Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)

(* To project field 0 out of a tuple, just grab the first component. *)
| Proj0 : forall v1 v2,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) 0) v1

(* To project field [1+n], drop the first component and continue with [n]. *)
| ProjS : forall v1 v2 n,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) (1 + n)) (Proj v2 n)
.

Inductive step : exp -> exp -> Prop :=
| StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.

Definition trsys_of (e : exp) :=
  {| Initial := {e}; Step := step |}.

(* Syntax of types *)
Inductive type :=
| Fun (dom ran : type)
| TupleTypeNil
| TupleTypeCons (t1 t2 : type)
.

Inductive subtype : type -> type -> Prop :=

(* Two function types are related if their components are related pairwise.
 * Counterintuitively, we *reverse* the comparison order for function domains!
 * It may be worth working through some examples to see why the relation would
 * otherwise be unsound. *)
| StFun : forall t1' t2' t1 t2,
    subtype t1 t1' ->
    subtype t2' t2 ->
    subtype (Fun t1' t2') (Fun t1 t2)

(* An empty tuple type is its own subtype. *)
| StTupleNilNil :
    subtype TupleTypeNil TupleTypeNil

(* However, a nonempty tuple type is also a subtype of the empty tuple type.
 * This rule gives rise to *width* subtyping, where we can drop some fields of
 * a tuple type to produce a subtype. *)
| StTupleNilCons : forall t1 t2,
    subtype (TupleTypeCons t1 t2) TupleTypeNil

(* We also have *depth* subtyping: we can replace tuple components with
 * subtypes. *)
| StTupleCons : forall t1' t2' t1 t2,
    subtype t1' t1 ->
    subtype t2' t2 ->
    subtype (TupleTypeCons t1' t2') (TupleTypeCons t1 t2)
.

(* Here's a more compact notation for subtyping. *)
Infix "$<:" := subtype (at level 70).

Local Hint Constructors subtype : core.

(* Projecting out the nth field of a tuple type *)
Inductive proj_t : type -> nat -> type -> Prop :=
| ProjT0 : forall t1 t2,
    proj_t (TupleTypeCons t1 t2) 0 t1
| ProjTS : forall t1 t2 n t,
    proj_t t2 n t ->
    proj_t (TupleTypeCons t1 t2) (1 + n) t
.

(* Expression typing relation stating something _has_ a _ty_pe *)
Inductive has_ty : fmap var type -> exp -> type -> Prop :=
| HtVar : forall G x t,
    G $? x = Some t ->
    has_ty G (Var x) t
| HtAbs : forall G x e1 t1 t2,
    has_ty (G $+ (x, t1)) e1 t2 ->
    has_ty G (Abs x e1) (Fun t1 t2)
| HtApp : forall G e1 e2 t1 t2,
    has_ty G e1 (Fun t1 t2) ->
    has_ty G e2 t1 ->
    has_ty G (App e1 e2) t2
| HtTupleNil : forall G,
    has_ty G TupleNil TupleTypeNil
| HtTupleCons: forall G e1 e2 t1 t2,
    has_ty G e1 t1 ->
    has_ty G e2 t2 ->
    has_ty G (TupleCons e1 e2) (TupleTypeCons t1 t2)
| HtProj : forall G e n t t',
    has_ty G e t' ->
    proj_t t' n t ->
    has_ty G (Proj e n) t

(* This is the crucial rule: when an expression has a type, it also has any
 * supertype of that type.  We call this rule *subsumption*. *)
| HtSub : forall G e t t',
    has_ty G e t' ->
    t' $<: t ->
    has_ty G e t
.

(* Before we get started proving properties of our type system, please read
 * Pset7Sig.v and consider the questions below. This task is
 * ungraded, but we are assigning it in hopes it helps you complete the
 * following parts.

 What does it mean for the subtyping order of the arguments in `StFun` to be 
 reversed?


 If t1 $<: t2, what is known about some t3 that is a supertype of t2? And 
 likewise if it's a subtype of t1?


 How many goals do you get from calling `invert` on a hypothesis like
 ```
 has_ty G (Abs x e1) t
 ```
 with the `LambdaCalculusAndTypeSoundness` definition of `has_ty`, and what 
 information do you have about `t`?

 To contrast, how many goals do you expect with the `has_ty` definition of
 this pset? Why is this the case? 

 Can you formulate a lemma that consolidates the information present in these 
 branches into one conclusion? (Imagine inverting now is equivalent to an
 "or" generating branches for each constructor; can you rephrase a lemma that
 leads to a conclusion with an "and" instead?)


 How many goals do you get from calling `invert` on a hypothesis like
 ```
 has_ty G e (Fun t1 t2)
 ```
 with the `LambdaCalculusAndTypeSoundness` definition of `has_ty`, and what 
 information do you have about `e`? 

 To contrast, how many goals do you expect with the `has_ty` definition 
 of this pset? Why is this the case? 

 Can you formulate a lemma to recover information similar to what inverting
 gave you in FRAP's `has_ty` definition?

*)

(* Prove these two basic algebraic properties of subtyping. *)

Lemma subtype_refl : forall t1, t1 $<: t1.
Proof.
  induct t1.
  - apply StFun; assumption.
  - apply StTupleNilNil.
  - apply StTupleCons; assumption.
Qed.

Ltac trans_tac :=
  match goal with
  | [ H1 : ?left $<: ?mid, H2 : ?mid $<: ?right, IH : _ |- ?left $<: ?right ]
    => destruct (IH mid right) as (Htrans, _); apply Htrans; assumption
  | [ H1 : ?left $<: ?mid, H2 : ?mid $<: ?right, IH : _ |- ?left $<: ?right ]
    => destruct (IH mid left) as (_, Htrans); apply Htrans; assumption
  end.

Lemma subtype_trans_helper t1 : forall t2 t3,
    (t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3) /\ (t3 $<: t2 -> t2 $<: t1 -> t3 $<: t1).
Proof.
  induct t1.
  - propositional.
    + invert H.
      invert H0.
      apply StFun; trans_tac.
    + invert H0.
      invert H.
      apply StFun; trans_tac.
  - propositional.
    + invert H.
      assumption.
    + invert H0.
      * assumption.
      * invert H.
        apply StTupleNilCons.
  - propositional.
    + invert H.
      * invert H0.
        apply StTupleNilCons.
      * invert H0.
        -- apply StTupleNilCons.
        -- apply StTupleCons; trans_tac.
    + invert H0.
      invert H.
      apply StTupleCons; trans_tac.
Qed.
        
(* HINT 1 (see Pset7Sig.v) *) 
Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
  intros.
  destruct (subtype_trans_helper t1 t2 t3).
  apply H1; assumption.
Qed.

(* BEGIN handy tactic that we suggest for these proofs *)
Ltac tac0 :=
  match goal with
  | [ H : ex _ |- _ ] => invert H
  | [ H : _ /\ _ |- _ ] => invert H
  | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
  | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify
  | [ H : step _ _ |- _ ] => invert H
  | [ H : step0 _ _ |- _ ] => invert1 H
  | [ H : has_ty _ _ _ |- _ ] => invert1 H
  | [ H : proj_t _ _ _ |- _ ] => invert1 H
  | [ H : plug _ _ _ |- _ ] => invert1 H
  | [ H : subtype _ _ |- _ ] => invert1 H
  | [ H : Some _ = Some _ |- _ ] => invert H
  end;
  subst.

Ltac tac := simplify; subst; propositional; repeat (tac0; simplify); try equality.
(* END handy tactic *)


(* The real prize: prove soundness of this type system.
 * We suggest starting from a copy of the type-safety proof from the book's
 * EvaluationContexts.v.
 * The soundness argument for simply typed lambda calculus is genuinely difficult
 * (a celebrated result!). We're not expecing you to reinvent it. Rather, the
 * task of this pset is to *extend* it to cover subtyping. This will involve
 * changing some proofs and making appropriate additional helper lemmas (there
 * are more hints in Pset7Sig.v).
 * Trying to write this proof from scratch is *not* recommended for this pset.
 * This is in contrast to the *previous* psets, which we tried to design so that
 * they could be solved from scratch with a good understanding of the lecture
 * material. *)

(* HINT 2-3 (see Pset7Sig.v) *)

Ltac teem := try (apply or_introl; equality); try (apply or_intror; equality).

Lemma var_equality_excluded_middle : forall (x : var) (y : var), (x = y) \/ (x <> y).
Proof.
  induct x; simplify.
  - cases y; teem.
  - cases y; teem.
    pose (IHx y).
    propositional; teem.
    cases a; cases a0; teem.
    cases b; cases b7; teem;
      cases b0; cases b8; teem;
      cases b1; cases b9; teem;
      cases b2; cases b10; teem;
      cases b3; cases b11; teem;
      cases b4; cases b12; teem;
      cases b5; cases b13; teem;
      cases b6; cases b14; teem.
Qed.

Lemma iDiedInsideWhenIRealizedIHadToProveThis_helper : forall e t G,
  has_ty G e t ->
  forall G',
  (forall x tx, G $? x = Some tx -> exists tx', tx' $<: tx /\G' $? x = Some tx') ->
  has_ty G' e t.
Proof.
  induct 1; simplify.
  - destruct H0 with (1 := H).
    destruct H1.
    apply HtSub with (t' := x0); auto.
    apply HtVar.
    assumption.
  - apply HtAbs.
    apply IHhas_ty.
    simplify.
    cases (var_equality_excluded_middle x x0).
    + exists tx.
      propositional.
      * apply subtype_refl.
      * rewrite <- e.
        simplify.
        assumption.
    + simplify.
      apply H0.
      assumption.
  - apply HtApp with (t1).
    + apply IHhas_ty1.
      assumption.
    + apply IHhas_ty2.
      assumption.
  - apply HtTupleNil.
  - apply HtTupleCons.
    + apply IHhas_ty1.
      assumption.
    + apply IHhas_ty2.
      assumption.
  - apply HtProj with (t').
    + apply IHhas_ty.
      assumption.
    + assumption.
  - apply HtSub with (t').
    + apply IHhas_ty.
      assumption.
    + assumption.
Qed.

Lemma iDiedInsideWhenIRealizedIHadToProveThis : forall x tx' tx e t,
  tx' $<: tx ->
  has_ty ($0 $+ (x, tx)) e t ->
  has_ty ($0 $+ (x, tx')) e t.
Proof.
  simplify.
  apply iDiedInsideWhenIRealizedIHadToProveThis_helper with (G := $0 $+ (x, tx)).
  - assumption.
  - simplify.
    cases (var_equality_excluded_middle x x0).
    + rewrite <- e0 in *.
      simplify.
      assert (tx0 = tx) by equality.
      rewrite H2.
      exists tx'.
      propositional.
    + simplify.
      discriminate.
Qed.

Corollary typeIndependent : forall e t G, has_ty $0 e t -> has_ty G e t.
Proof.
  simplify.
  apply iDiedInsideWhenIRealizedIHadToProveThis_helper with (G := $0); auto.
Qed.

Lemma iDiedOutsideWhenIRealizedIHadToProveThis_helper : forall e t G,
  has_ty G e t ->
  forall x tx v,
  G $? x = Some tx ->
  has_ty $0 v tx ->
  forall G',
  (forall y, x <> y -> G $? y = G' $? y) ->
  has_ty G' (subst v x e) t.
Proof.
  induct 1; simplify.
  - cases (x ==v x0).
    + rewrite e in H.
      rewrite H0 in H.
      assert (t = tx) by equality.
      rewrite H3.
      apply typeIndependent.
      assumption.
    + apply HtVar.
      assert (x0 <> x) by equality.
      pose (H2 x H3).
      equality.
  - cases (x ==v x0).
    + apply HtAbs.
      rewrite <- e in *.
      assert (G $+ (x, t1) = G' $+ (x, t1)).
      * apply fmap_ext.
        simplify.
        cases (var_equality_excluded_middle k x); simplify.
        -- equality.
        -- apply H2.
           equality.
      * rewrite <- H3.
        assumption.
    + apply HtAbs.
      apply IHhas_ty with (G' := G' $+ (x, t1)) (tx := tx).
      * simplify.
        assumption.
      * assumption.
      * simplify.
        cases (var_equality_excluded_middle y x); simplify; auto.
  - apply HtApp with (t1).
    + apply IHhas_ty1 with (tx); assumption.
    + apply IHhas_ty2 with (tx); assumption.
  - apply HtTupleNil.
  - apply HtTupleCons.
    + apply IHhas_ty1 with (tx); assumption.
    + apply IHhas_ty2 with (tx); assumption.
  - apply HtProj with (t').
    + apply IHhas_ty with (tx); assumption.
    + assumption.
  - apply HtSub with (t').
    + apply IHhas_ty with (tx); assumption.
    + assumption.
Qed.

Lemma iDiedOutsideWhenIRealizedIHadToProveThis : forall e t x tx v,
  has_ty $0 v tx ->
  has_ty ($0 $+ (x, tx)) e t ->
  has_ty $0 (subst v x e) t.
Proof.
  simplify.
  apply iDiedOutsideWhenIRealizedIHadToProveThis_helper with (G := $0 $+ (x, tx)) (tx := tx); auto.
  - simplify.
    equality.
  - simplify.
    equality.
Qed.

Lemma ifItsATupleThenItsATuple : forall v t1 t2,
  value v ->
  has_ty $0 v (TupleTypeCons t1 t2) ->
  exists v1 v2, v = TupleCons v1 v2 /\ has_ty $0 v1 t1 /\ has_ty $0 v2 t2.
Proof.
  induct 2; simplify.
  - discriminate.
  - invert H.
  - exists e1.
    exists e2.
    propositional.
  - invert H.
  - invert H1.
    destruct (IHhas_ty t1' t2' H eq_refl eq_refl).
    destruct H1.
    destruct H1.
    exists x.
    exists x0.
    propositional.
    + apply HtSub with (t' := t1'); assumption.
    + apply HtSub with (t' := t2'); assumption.
Qed.

Lemma ifItsAFunctionThenItsAFunction : forall v t1 t2,
  value v ->
  has_ty $0 v (Fun t1 t2) ->
  exists x e, v = Abs x e /\ has_ty ($0 $+ (x, t1)) e t2.
Proof.
  induct 2; simplify.
  - discriminate.
  - exists x.
    exists e1.
    propositional.
  - invert H.
  - invert H.
  - invert H1.
    destruct (IHhas_ty t1' t2' H eq_refl eq_refl).
    destruct H1.
    destruct H1.
    exists x.
    exists x0.
    propositional.
    apply HtSub with (t' := t2').
    + apply iDiedInsideWhenIRealizedIHadToProveThis with (tx := t1'); assumption.
    + assumption.
Qed.

Lemma typeSame0 : forall e e' t,
  has_ty $0 e t -> step0 e e' -> has_ty $0 e' t.
Proof.
  induct 1; simplify.
  - discriminate.
  - invert H0.
  - invert H1.
    invert H.
    + apply iDiedOutsideWhenIRealizedIHadToProveThis with (tx := t1); assumption.
    + destruct ifItsAFunctionThenItsAFunction with (t1 := t1) (t2 := t2) (v := Abs x e).
      * apply VAbs.
      * apply HtSub with (t'); assumption.
      * destruct H.
        destruct H.
        assert (x0 = x) by equality.
        rewrite H4 in H3.
        assert (x1 = e) by equality.
        rewrite H6 in H3.
        apply iDiedOutsideWhenIRealizedIHadToProveThis with (tx := t1); assumption.
  - invert H.
  - invert H1.
  - invert H1.
    + invert H0.
      destruct (ifItsATupleThenItsATuple (VTupleCons H4 H6) H).
      destruct H0.
      propositional.
      assert (e' = x) by equality.
      rewrite H2.
      assumption.
    + invert H0.
      destruct (ifItsATupleThenItsATuple (VTupleCons H4 H6) H).
      destruct H0.
      propositional.
      apply HtProj with (t' := t2).
      * assert (v2 = x0) by equality.
        rewrite H2.
        assumption.
      * assumption.
  - apply HtSub with (t'); auto.
Qed.

Lemma appTypedImplies : forall e1 e2 t',
  has_ty $0 (App e1 e2) t' ->
  exists t, has_ty $0 e1 (Fun t t') /\ has_ty $0 e2 t.
Proof.
  induct 1.
  - eauto.
  - destruct IHhas_ty.
    exists x.
    propositional.
    apply HtSub with (t' := Fun x t'); auto.
    apply StFun; auto.
    apply subtype_refl.
Qed.

Lemma consTypedImplies : forall e1 e2 t,
  has_ty $0 (TupleCons e1 e2) t ->
  exists t1 t2, (t = TupleTypeNil \/ t = TupleTypeCons t1 t2) /\ has_ty $0 e1 t1 /\ has_ty $0 e2 t2.
Proof.
  induct 1.
  - eauto 7.
  - destruct IHhas_ty as (t1, H1).
    destruct H1 as (t2, H1).
    propositional.
    + invert H0; try discriminate.
      eauto 7.
    + invert H0; try discriminate.
      * eauto 7.
      * exists t0.
        exists t3.
        propositional.
        -- apply HtSub with (t' := t1'); auto.
           assert (t1' = t1) by equality.
           rewrite H0.
           assumption.
        -- apply HtSub with (t' := t2'); auto.
           assert (t2' = t2) by equality.
           rewrite H0.
           assumption.
Qed.

Lemma projTyped_helper : forall n t' tn tn',
  proj_t t' n tn' ->
  tn' $<: tn ->
  exists t, t' $<: t /\ proj_t t n tn.
Proof.
  induct n; tac.
  - exists (TupleTypeCons tn t2).
    propositional.
    + apply StTupleCons.
      * assumption.
      * apply subtype_refl.
    + apply ProjT0.
  - destruct (IHn t2 tn tn'); auto.
    exists (TupleTypeCons t1 x).
    propositional.
    + apply StTupleCons.
      * apply subtype_refl.
      * assumption.
    + apply ProjTS.
      assumption.
Qed.

Lemma projTypedImplies : forall n e t,
  has_ty $0 (Proj e n) t ->
  exists t', has_ty $0 e t' /\ proj_t t' n t.
Proof.
  induct 1.
  - eauto.
  - destruct IHhas_ty.
    destruct H1.
    destruct (projTyped_helper H2 H0).
    exists x0.
    propositional.
    apply (HtSub H1 H4).
Qed.

Lemma holeStepTypeSame : forall e1 e2 C t e1' e2',
  step0 e1 e2 ->
  has_ty $0 e1' t ->
  plug C e1 e1' ->
  plug C e2 e2' ->
  has_ty $0 e2' t.
Proof.
  induct C; simplify; invert H1; invert H2.
  - apply typeSame0 with (e := e1'); assumption.
  - destruct (appTypedImplies H0).
    destruct H1.
    apply HtApp with (t1 := x).
    + apply IHC with (e1' := e'); auto.
    + assumption.
  - destruct (appTypedImplies H0).
    destruct H1.
    apply HtApp with (t1 := x).
    + assumption.
    + apply IHC with (e1' := e'); auto.
  - destruct (consTypedImplies H0).
    destruct H1.
    propositional.
    + apply HtSub with (t' := TupleTypeCons x x0).
      * apply HtTupleCons.
        -- apply IHC with (e1' := e'); auto.
        -- assumption.
      * rewrite H3.
        apply StTupleNilCons.
    + rewrite H3.
      apply HtTupleCons.
      * apply IHC with (e1' := e'); auto.
      * assumption.
  - destruct (consTypedImplies H0).
    destruct H1.
    propositional.
    + apply HtSub with (t' := TupleTypeCons x x0).
      * apply HtTupleCons.
        -- assumption.
        -- apply IHC with (e1' := e'); auto.
      * rewrite H3.
        apply StTupleNilCons.
    + rewrite H3.
      apply HtTupleCons.
      * assumption.
      * apply IHC with (e1' := e'); auto.
  - destruct (projTypedImplies H0).
    destruct H1.
    apply HtProj with (t' := x).
    + apply IHC with (e1' := e'); auto.
    + assumption.
Qed.

Lemma typeSame : forall e e' t,
  has_ty $0 e t -> step e e' -> has_ty $0 e' t.
Proof.
  induct 2.
  apply holeStepTypeSame  with (C := C) (e1 := e1) (e2 := e2) (e1' := e1'); auto.
Qed.

Lemma typeSameGeneral : forall e e' t,
  has_ty $0 e t -> (step) ^* e e' -> has_ty $0 e' t.
Proof.
  simplify.
  induct H0.
  - assumption.
  - apply IHtrc.
    apply typeSame with (e := x); assumption.
Qed.


Lemma stepWithHole : forall e1 e2,
  step0 e1 e2 -> step e1 e2.
Proof.
  simplify.
  apply (StepRule (PlugHole e1) (PlugHole e2) H).
Qed.

Ltac plug_tac P := try apply P; auto.

Lemma safetyOne : forall e t,
  has_ty $0 e t -> value e \/ exists e', step e e'.
Proof.
  induct 1.
  - simplify.
    discriminate.
  - apply or_introl.
    apply VAbs.
  - apply or_intror.
    simplify.
    assert (value e1 \/ (exists e' : exp, step e1 e')).
    + apply IHhas_ty1.
      equality.
    + cases H1.
      * pose (ifItsAFunctionThenItsAFunction H1 H).
        tac.
        -- exists (subst e2 x x0).
           apply stepWithHole.
           apply Beta.
           assumption.
        -- exists (App (Abs x0 x1) x).
           apply StepRule with (C := App2 (Abs x0 x1) C) (e1 := e1) (e2 := e0);
             plug_tac PlugApp2.
      * destruct H1.
        destruct H1.
        exists (App e2' e2).
        apply StepRule with (C := App1 C e2) (e1 := e1) (e2 := e0);
          plug_tac PlugApp1.
  - apply or_introl.
    apply VTupleNil.
  - assert (value e1 \/ (exists e' : exp, step e1 e')).
    + apply IHhas_ty1.
      equality.
    + cases H1.
      * cases IHhas_ty2.
        -- apply or_introl.
           apply VTupleCons; assumption.
        -- apply or_intror.
           destruct IHhas_ty2.
           destruct H2.
           exists (TupleCons e1 e2').
           apply StepRule with (C := TupleCons2 e1 C) (e1 := e0) (e2 := e2);
             plug_tac PlugTupleCons2.
      * apply or_intror.
        destruct H1.
        destruct H1.
        exists (TupleCons e2' e2).
        apply StepRule with (C := TupleCons1 C e2) (e1 := e1) (e2 := e0);
          plug_tac PlugTupleCons1.
  - apply or_intror.
    tac.
    + invert H0.
      * pose (ifItsATupleThenItsATuple H1 H).
        tac.
        exists x.
        apply stepWithHole.
        invert H1.
        apply Proj0; assumption.
      * pose (ifItsATupleThenItsATuple H1 H).
        tac.
        exists (Proj x0 n0).
        apply stepWithHole.
        invert H1.
        apply ProjS; assumption.
    + exists (Proj x n).
      apply StepRule with (C := Proj1 C n) (e1 := e1) (e2 := e2);
        plug_tac PlugProj.
  - assumption.
Qed.

Theorem safety :
  forall e t,
    has_ty $0 e t -> invariantFor (trsys_of e)
                                  (fun e' => value e'
                                             \/ exists e'', step e' e'').
Proof.
  simplify.
  unfold invariantFor.
  simplify.
  propositional.
  rewrite H2 in *.
  apply safetyOne with (t := t).
  apply typeSameGeneral with (e := s); assumption.
Qed.

End Impl.

(* The following line checks that your `Impl` module implements the right
   signature.  Make sure that it works, or the auto-grader will break!
   If there are mismatches, Coq will report them (`Signature components for
   label \u2026 do not match`): *)
Module ImplCorrect : Pset7Sig.S := Impl.

(* Authors:
 * Peng Wang
 * Adam Chlipala
 * Samuel Gruetter
 * Amanda Liu
 *)
