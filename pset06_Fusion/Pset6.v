(** * 6.512 Formal Reasoning About Programs, Spring 2023 - Pset 6 *)
Require Import Frap.Frap Pset6.Pset6Sig.
Import Swap.

(*Module Swap.

  Local Definition swap' {A} (n1 n2 : nat) (l : list A) default :=
    firstn n1 l ++ (nth n2 l default)::(firstn (n2 - S n1) (skipn (S n1) l))
      ++ (nth n1 l default)::(skipn (S n2) l).


  (* Assumption: n1 < n2 < length l *)
  (* uses some tricks to avoid a default element and to make lemmas easier to use *)
  Definition swap {A} (n1 n2 : nat) (l : list A) :=
    if (Nat.leb n2 n1) || (Nat.leb (length l) n2) then l
    else match l with
         | [] => []
         | a::_ => swap' n1 n2 l a
         end.


  Lemma Forall2_nth A B R l1 l2 (a:A) (b:B)
    : Forall2 R l1 l2 ->
      forall n,
        n < length l2 ->
        R (nth n l1 a) (nth n l2 b).
  Proof.
    induct 1;
      simplify;
      try linear_arithmetic;
      auto.
    cases n;
      simplify; eauto.
    apply IHForall2;
      try linear_arithmetic;
      auto.
  Qed.

  Local Hint Constructors Forall2 : core.

  Lemma Forall2_ext A B (R : A -> B -> Prop)
    : forall l1 l2,
      (forall n a b, n < length l2 -> R (nth n l1 a) (nth n l2 b)) ->
      length l1 = length l2 ->
      Forall2 R l1 l2.
  Proof.
    induct l1;
      simplify;
      cases l2;
      simplify;
      auto;
      try linear_arithmetic.
    invert H0.
    pose proof (fun n => H (S n)).
    pose proof (H 0).
    clear H.
    simplify.
    first_order.
    constructor; eauto.
    {
      apply H1; auto; linear_arithmetic.
    }
    {
      apply IHl1; auto.
      simplify; apply H0; linear_arithmetic.
    }
  Qed.


  Local Lemma length_swap' A (l : list A) n1 n2 a
    : n1 < n2 ->
      n2 < length l ->
      length (swap' n1 n2 l a) = length l.
  Proof.
    unfold swap'.
    intros.
    repeat (rewrite ?app_length, ?firstn_length, ?skipn_length; cbn [length]).
    rewrite Nat.min_l by linear_arithmetic.
    rewrite Nat.min_l by linear_arithmetic.
    linear_arithmetic.
  Qed.  

  Lemma length_swap A (l : list A) n1 n2
    : length (swap n1 n2 l) = length l.
  Proof.
    unfold swap.
    destruct (Nat.leb_spec n2 n1);
      simplify; auto.
    destruct (Nat.leb_spec (length l) n2);
      simplify; auto.
    cases l; auto.
    apply length_swap'; auto.
  Qed.
  Global Hint Rewrite length_swap : core.


  Lemma Forall2_length A B (R: A -> B -> Prop) l1 l2
    : Forall2 R l1 l2 ->
      length l1 = length l2.
  Proof.
    induct 1; simplify; eauto.
  Qed.
  Global Hint Resolve Forall2_length : core.


  Lemma Forall2_app A B (R : A -> B -> Prop) l11 l12 l21 l22
    : Forall2 R l11 l12 ->
      Forall2 R l21 l22 ->
      Forall2 R (l11++l21) (l12++l22).
  Proof.
    induct 1; simplify; eauto.
  Qed.

  Lemma Forall2_firstn A B (R : A -> B -> Prop) l1 l2
    : Forall2 R l1 l2 ->
      forall n,
        Forall2 R (firstn n l1) (firstn n l2).
  Proof.
    induct 1; simplify; cases n; simplify; eauto.
  Qed.
  
  Lemma Forall2_skipn A B (R : A -> B -> Prop) l1 l2
    : Forall2 R l1 l2 ->
      forall n,
        Forall2 R (skipn n l1) (skipn n l2).
  Proof.
    induct 1; simplify; cases n; simplify; eauto.
  Qed.  

  Local Lemma Forall2_swap' A B (R : A -> B -> Prop) l1 l2 a b
    : Forall2 R l1 l2 ->
      forall n1 n2,
        n1 < n2 ->
        n2 < length l2 ->
        Forall2 R (swap' n1 n2 l1 a) (swap' n1 n2 l2 b).
  Proof.
    unfold swap'.
    intros.
    repeat first
      [ assumption
      | apply Forall2_app
      | apply Forall2_firstn
      | apply Forall2_skipn
      | apply List.Forall2_cons
      | apply Forall2_nth].
    linear_arithmetic.
  Qed.  

  Lemma Forall2_swap A B (R : A -> B -> Prop) l1 l2
    : Forall2 R l1 l2 ->
      forall n1 n2,
        Forall2 R (swap n1 n2 l1) (swap n1 n2 l2).
  Proof.
    intros.
    unfold swap.
    destruct (Nat.leb_spec n2 n1);
      simplify; auto.
    pose proof (Forall2_length _ _ _ _ _ H) as Hlen;
      rewrite Hlen.
    destruct (Nat.leb_spec (length l2) n2);
      simplify; auto.
    cases l1; cases l2; simplify; try linear_arithmetic.
    apply Forall2_swap'; simplify; propositional.
  Qed.
  Global Hint Resolve Forall2_swap : core.


  Local Lemma app_swap'1
    : forall (A : Type) (l l' : list A) (n1 n2 : nat) a,
      n1 < n2 -> n2 < Datatypes.length l -> swap' n1 n2 (l ++ l') a = (swap' n1 n2 l a)++l'.
  Proof.
    intros.
    unfold swap'.
    rewrite !firstn_app, !skipn_app, !app_nth1 by linear_arithmetic.
    repeat (replace (_ - length l) with 0 by linear_arithmetic).
    repeat change (firstn 0 _) with (@nil A).
    repeat change (skipn 0 ?l) with l.
    rewrite !app_nil_r.
    rewrite <- !app_assoc.
    rewrite !firstn_app.
    rewrite skipn_length.
    replace (n2 - S n1 - (Datatypes.length l - S n1)) with 0 by linear_arithmetic.
    repeat change (firstn 0 _) with (@nil A).
    rewrite !app_nil_r.
    
    cbn [app].
    rewrite <- !app_assoc.
    reflexivity.
  Qed.
  
  Lemma app_swap1
    : forall (A : Type) (l l' : list A) (n1 n2 : nat),
      n1 < n2 -> n2 < Datatypes.length l -> 
      swap n1 n2 (l ++ l') = (swap n1 n2 l)++l'.
  Proof.
    simplify.
    unfold swap. 
    destruct (Nat.leb_spec n2 n1);
      simplify; auto.
    destruct (Nat.leb_spec (length l) n2);
      simplify; try linear_arithmetic.
    destruct (Nat.leb_spec (length (l ++ l')) n2);
      simplify; rewrite app_length in *; try linear_arithmetic.
    cases l; simplify; try linear_arithmetic.
    change (a :: l ++ l') with ((a::l)++l').
    apply app_swap'1; auto.
  Qed.

End Swap.

Import Swap.*)


(*|
Modern compilers achieve excellent performance by leveraging a wide variety of
program transformations.  For example, GCC (the GNU C compiler) version 10.2
produces the *exact same* assembly code for the following two programs (if you
want to see for yourself, try it on https://godbolt.org!):

1. Recursive version with accumulator, naive division and modulo, no function
   inlining, multiple returns, redundant ``+ 1``, not tail-recursive::

      static unsigned int affine(unsigned int n,
                                 unsigned int slope,
                                 unsigned int offset) {
          return n * slope + offset;
      }

      unsigned int collatz1(unsigned int start) {
          if (start == 1)
            return 0;
          else if (start % 2 == 0)
            return collatz1(start / 2) + 1;
          else
            return collatz1(affine(start, 3, 1)) + 1;
      }

2. Single loop, inlined function, bitwise arithmetic::

      unsigned int collatz2(unsigned int start) {
          unsigned int flight = 0;
          while (start != 1) {
              flight++;
              if ((start & 1) == 0) {
                  start = start >> 1;
              } else {
                  start = start * 2 + start + 1;
              }
          }
          return flight;
      }

The way GCC achieves this is by applying a sequence of transformation passes on
the code: you can see the output of each intermediate pass (all ~320 of them)
using ``gcc -O3 -fdump-tree-all -fdump-rtl-all -c collatz1.c``.  For instance,
the ``ssa`` pass puts the code into a form similar to the three-address code
that we saw in class, the ``tailr1`` passes convert the recursive function to a
loop, etc.

Students interested in an introduction to the magic of modern compiler
optimizations might enjoy Matt Godbolt's 2017 talk at CPPCon, *What Has My
Compiler Done for Me Lately? Unbolting the Compiler's Lid*
(https://www.youtube.com/watch?v=bSkpMdDe4g4).

In this lab, we'll see how formal methods can help us reason about the
correctness of these optimization passes, focusing on a couple of particular
optimizations.

Pset6Sig.v contains the number of points you get for each definition and
proof. Note that since we ask you to come up with some definitions
yourself, all proofs being accepted by Coq does not necessarily guarantee a
full score: you also need to make sure that your definitions correspond to
what we ask for in the instructions. That said, if the required tests pass
and your definitions do not intentionally special-case them, you should be
fine.

*A few notes of caution*:

- Some of the proofs in this lab can be a bit long to complete fully manually:
  we encourage you to try your hand at simple automation.  However, make sure
  that your whole file compiles in a reasonable amount of time (at most a minute
  or two).

- When decomposed into the right sequence of lemmas, most of the theorems in
  this pset have relatively short proofs.  The best way to find these lemmas is
  to approach each problem cautiously, trying to work an understanding of the
  proof before diving into long series of `invert`, `econstructor`, etc.  In
  general, it's also a good idea to admit lemmas until you are sure that they
  allow you to prove the complete theorem, then go back and prove the lemmas \u2014
  but do take the time to convince yourself that your lemmas make sense, so that
  you don't waste time using incorrect lemmas.

- We have included plenty of hints below in the HINTS section of the 
  signature file.
|*)

Module Impl.

(*
  We'll be working with a small stack-based language in this lab, where we
  interpret a program as a transformation from an input stack to an output stack,
  primarily done by pushing and popping values on and off the stack.
 *)

(*
  Our values consist of natural numbers and lists of values.
  So that we can have a single value type, we use the following datatype:
 *)
Inductive stack_val :=
| val_lit (n : nat)
| val_nil
| val_cons (v1 v2 : stack_val).

(*
  However, this inductive definition admits expressions that do not conform
  to our English definition of our set of values. For example, the following
  term has the Coq type `stack_val`: `val_cons (val_lit 0) (val_lit 1)`, even
  though we see it as ill-formed since the tail of a cons should be a list.
  In order to describe the set of well-formed values, we define the following
  datatype of stack-language type signatures and an associated typing judgment
  for stack values.

  The typing judgments in this lab are fairly straightforward since they only
  have to be concerned with natural numbers and lists, but you can think of them
  as a preview of the sort of problems that will be in next week's assignment.
 *)
Inductive ty : Set :=
| ty_nat
| ty_list (t : ty).

Inductive val_well_typed : stack_val -> ty -> Prop :=
| val_lit_wt n : val_well_typed (val_lit n) ty_nat
| val_nil_wt t : val_well_typed val_nil (ty_list t)
| val_cons_wt t v1 v2
  : val_well_typed v1 t ->
      val_well_typed v2 (ty_list t) ->
      val_well_typed (val_cons v1 v2) (ty_list t).
Local Hint Constructors val_well_typed : core.

(*
  Since a stack is a list of values, we can use this judgment to define
  a typing judgments for stacks as well. The type of a stack is just a list
  of the types of its values. Since `val_well_typed` is a binary relation,
  we can use `Forall2` from the standard library to lift it to operate on stacks.
  You can see the definition of `Forall2` by printing it:
 *)
Print Forall2.

(*
  We define `stack_well_typed` as a notation instead of a definition for some
  convenience in tactics. You don't need to pay attention to the difference
  except to know that you can't unfold `stack_well_typed`, but Coq automatically
  will see it as a use of `Forall2`.
 *)
Notation stack_well_typed := (Forall2 val_well_typed).
Local Hint Constructors Forall2 : core.


(* Here are some definitions that we will use in the interpreter.
   Many of them have dummy cases that we do not expect to hit.
   Specifically, the benefit of all of the typing judgments is that
   they guarantee these cases will never happen. 
 *)

Definition stack_unop f (s : list stack_val) :=
  match s with
  | a::s' => (f a)::s'
  | _ => (*this case never happens on well-typed programs*) s
  end.

Definition stack_binop f (s : list stack_val) :=
  match s with
  | a::b::s' => (f a b)::s'
  | _ => (*this case never happens on well-typed programs*) s
  end.



Definition stack_pop (s : list stack_val) :=
  match s with
  | a::s => (a,s)
  | _ => (*this case never happens on well-typed programs*) (val_lit 0, [])
  end.

Definition stack_peek (s : list stack_val) :=
  match s with
  | a::_ => a
  | _ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Fixpoint val_app v1 v2 :=
  match v1 with
  | val_nil => v2
  | val_cons v11 v12 => val_cons v11 (val_app v12 v2)
  | val_lit _ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Fixpoint val_flatmap (f : stack_val -> stack_val) v :=
  match v with
  | val_nil => val_nil
  | val_cons v1 v2 =>
      val_app (f v1) (val_flatmap f v2)
  | val_lit _ => val_lit 0
  end.

Fixpoint val_reduce (f : stack_val -> stack_val -> stack_val) vl vacc :=
  match vl with
  | val_nil => vacc
  | val_cons v1 v2 =>
      val_reduce f v2 (f vacc v1)
  | val_lit _ => val_lit 0
  end.


(*
  You will have to prove some lemmas about most of these functions to finish
  the later exercises. We've given you one of the more complicated ones here
  to prove, but you should come up with your own for the other functions as
  needed.
 *)

Lemma val_app_sound t l1 l2 :
    val_well_typed l1 (ty_list t) ->
    val_well_typed l2 (ty_list t) ->
    val_well_typed (val_app l1 l2) (ty_list t).
Proof.
  induct l1; simplify.
  - invert H.
  - assumption.
  - apply val_cons_wt.
    + invert H.
      assumption.
    + apply IHl1_2.
      * invert H.
        assumption.
      * assumption.
Qed.

Lemma val_flatmap_sound t1 t2 f l
  : (forall x, val_well_typed x t1 -> val_well_typed (f x) (ty_list t2)) ->
    val_well_typed l (ty_list t1) ->
    val_well_typed (val_flatmap f l) (ty_list t2).
Proof.
  induct l; simplify.
  - invert H0.
  - apply val_nil_wt.
  - invert H0.
    pose (H l1 H4).
    apply val_app_sound.
    + assumption.
    + apply IHl2; assumption.
Qed.

Lemma val_reduce_sound t tacc f l vacc :
  (forall x y, val_well_typed x tacc -> val_well_typed y t -> val_well_typed (f x y) tacc) ->
  val_well_typed vacc tacc ->
  val_well_typed l (ty_list t) ->
  val_well_typed (val_reduce f l vacc) tacc.
Proof.
  induct l; simplify.
  - invert H1.
  - assumption.
  - invert H1.
    apply IHl2.
    + assumption.
    + apply H; assumption.
    + assumption.
Qed.


Lemma stack_peek_sound t S s :
    stack_well_typed s (t :: S) ->
    val_well_typed (stack_peek s) t.
Proof.
  simplify.
  invert H.
  simplify.
  assumption.
Qed.

Lemma val_flatmap_same f g l t:
  (forall x, val_well_typed x t -> f x = g x) ->
  val_well_typed l (ty_list t) ->
  val_flatmap f l = val_flatmap g l.
Proof.
  induct l; simplify.
  - equality.
  - equality.
  - invert H0.
    rewrite H; auto.
    rewrite IHl2 with (t := t); auto.
Qed.

Lemma val_reduce_same f g l vacc tacc t:
  (forall x y, val_well_typed x tacc -> val_well_typed y t -> val_well_typed (f x y) tacc) ->
  (forall x y, val_well_typed x tacc -> val_well_typed y t -> val_well_typed (g x y) tacc) ->
  (forall x y, val_well_typed x tacc -> val_well_typed y t -> f x y = g x y) ->
  val_well_typed l (ty_list t) ->
  val_well_typed vacc tacc ->
  val_reduce f l vacc = val_reduce g l vacc.
Proof.
  induct l; simplify.
  - equality.
  - equality.
  - invert H2.
    rewrite H1; auto.
    rewrite IHl2 with (t := t) (tacc := tacc); auto.
Qed.

(*
  Now that we have values, we can define our syntax of commands.
  Their purposes are as follows:
  - cmd_atom: push a value onto the stack
  - cmd_unop: pop a value from the stack, perform an unary operation on it,
              and push the result back
  - cmd_binop: pop two values from the stack, perform a binary operation on them,
              and push the result back
  - cmd_swap: switch 2 values in the stack, determined by their positions.
              `n1` must always be the earlier (smaller) position.
  - cmd_flatmap: the most interesting operation in this assignment. It pops a
                 list value from the stack, runs a command `cf` on each element of
                 the list, and appends the outputs of that command in order.
  - cmd_reduce: pops a list value and another value from the stack and accumulates
                an output value by starting with the second value and running
                a command `cf` on the current accumulator and each item in the list
                in turn.
  - cmd_skip: All other commands take the rest of the program as their final arguments.
              We use `cmd_skip` when we want to end the current command.

  You may notice that we're playing a little trick here with cmd_unop and cmd_binop.
  These cases of our stack language actually take in Coq functions directly.
  This has some drawbacks, but it allows us to use these two constructors to add
  all sorts of operations to our language, from arithmetic to cons and ranges.
 *)
Inductive stack_cmd :=
| cmd_atom (v : stack_val) (c : stack_cmd)
| cmd_unop (f : stack_val -> stack_val) (c : stack_cmd)
| cmd_binop (f : stack_val -> stack_val -> stack_val) (c : stack_cmd)
| cmd_swap (n1 n2 : nat) (c : stack_cmd)
| cmd_flatmap (cf : stack_cmd) (c : stack_cmd)
| cmd_reduce (cf : stack_cmd) (c : stack_cmd)
| cmd_skip.



(*
  This is the typing judgment for commands. You should read `cmd_well_typed S c S'`
  as "On an input stack of type S, running c must produce an output stack of type S'".

  Notice that in the flatmap and reduce cases, `cf` only works with fixed input and
  output stacks. This means that it's not allowed to affect the rest of the stack,
  for example by swapping with some earlier value.
 *)
Inductive cmd_well_typed : list ty -> stack_cmd -> list ty -> Prop :=
| cmd_atom_wt v t S c S'
  : val_well_typed v t ->
    cmd_well_typed (t::S) c S' ->
    cmd_well_typed S (cmd_atom v c) S'
| cmd_unop_wt f t1 t2 S c S'
  : (forall v, val_well_typed v t1 -> val_well_typed (f v) t2) ->
    cmd_well_typed (t2::S) c S' ->
    cmd_well_typed (t1::S) (cmd_unop f c) S'
| cmd_binop_wt f t1 t2 t3 S c S'
  : (forall v1 v2, val_well_typed v1 t1 ->
                   val_well_typed v2 t2 ->
                   val_well_typed (f v1 v2) t3) ->
    cmd_well_typed (t3::S) c S' ->
    cmd_well_typed (t1::t2::S) (cmd_binop f c) S'
| cmd_swap_wt S n1 n2 c S'
  : n1 < n2 ->
    n2 < length S ->
    cmd_well_typed (swap n1 n2 S) c S' ->
    cmd_well_typed S (cmd_swap n1 n2 c) S'
| cmd_flatmap_wt S (cf : stack_cmd) t1 t2 c S'
  : cmd_well_typed ((ty_list t2)::S) c S' ->
    cmd_well_typed [t1] cf [ty_list t2] ->
    cmd_well_typed ((ty_list t1)::S) (cmd_flatmap cf c) S'
| cmd_reduce_wt S (cf : stack_cmd) t t_acc c S'
  : cmd_well_typed (t_acc::S) c S' ->
    cmd_well_typed [t; t_acc] cf [t_acc] ->
    cmd_well_typed ((ty_list t)::t_acc::S) (cmd_reduce cf c) S'
| cmd_skip_wt S
  : cmd_well_typed S (cmd_skip) S.
Local Hint Constructors cmd_well_typed : core.


(*
  This is our interpreter, which defines the behavior of our programs.
  Since all programs in this language terminate, we can define it as a
  regular Coq function that takes a command and a stack and runs the
  command against the stack.
 *)
Fixpoint interp_cmd (c : stack_cmd) (s : list stack_val) : list stack_val :=
  match c with
  | cmd_atom v c' => interp_cmd c' (v::s)
  | cmd_unop f c' => interp_cmd c' (stack_unop f s)
  | cmd_binop f c' => interp_cmd c' (stack_binop f s)
  | cmd_swap n1 n2 c' => interp_cmd c' (swap n1 n2 s)
  | cmd_flatmap cf c' =>
      let (l,s1) := stack_pop s in
      let out := val_flatmap (fun x => stack_peek (interp_cmd cf [x])) l in
      interp_cmd c' (out::s1)
  | cmd_reduce cf c' => 
      let (l,s) := stack_pop s in
      let (acc,s) := stack_pop s in
      let out := val_reduce (fun acc x => stack_peek (interp_cmd cf [x;acc])) l acc in
      interp_cmd c' (out::s)
  | cmd_skip => s
  end.









(*
  Now let's prove that our interpreter satisfies our typing judgment.
  In other words, that running a well-typed command on a well-typed
  input stack produces a well-typed output stack.

  HINT: If you aren't sure what to do in the `cmd_reduce` case,
  look at `val_flatmap_sound` for inspiration.
  If you're really stuck, read HINT 1 in Pset6Sig.v.
 *)

Lemma interp_sound_helper c S S'
  : cmd_well_typed S c S' ->
    forall s, stack_well_typed s S ->
              stack_well_typed (interp_cmd c s) S'.
Proof.
  induct c; simplify; invert H.
  - apply IHc with (S := t :: S).
    + assumption.
    + apply Forall2_cons;
        assumption.
  - apply IHc with (S := t2 :: S0).
    + assumption.
    + invert H0.
      simplify.
      apply Forall2_cons.
      * apply H4.
        assumption.
      * assumption.
  - apply IHc with (S := t3 :: S0).
    + assumption.
    + invert H0.
      invert H5.
      simplify.
      apply Forall2_cons.
      * apply H4; assumption.
      * assumption.
  - apply IHc with (S := swap n1 n2 S).
    + assumption.
    + apply Forall2_swap.
      assumption.
  - invert H0.
    simplify.
    apply IHc2 with (S := ty_list t2 :: S0).
    + assumption.
    + apply Forall2_cons.
      * apply val_flatmap_sound with (t1 := t1).
        -- simplify.
           apply stack_peek_sound with (S := []).
           apply IHc1 with (S := [t1]).
           ++ assumption.
           ++ apply Forall2_cons; auto.
        -- assumption.
      * assumption.
  - invert H0.
    invert H5.
    simplify.
    apply IHc2 with (S := t_acc :: S0).
    + assumption.
    + apply Forall2_cons.
      * apply val_reduce_sound with (t := t).
        -- simplify.
           apply stack_peek_sound with (S := []).
           apply IHc1 with (S := [t; t_acc]).
           ++ assumption.
           ++ apply Forall2_cons.
              ** assumption.
              ** apply Forall2_cons; auto.
        -- assumption.
        -- assumption.
      * assumption.
  - assumption.
Qed.


Lemma interp_sound S c S'
  : cmd_well_typed S c S' ->
    forall s, stack_well_typed s S ->
              stack_well_typed (interp_cmd c s) S'.
Proof.
  apply interp_sound_helper.
Qed.
  

(*
  Sometimes it's useful to combine two sequences of commands.
  Define a function `cmd_seq` so that the output is the
  concatenation of its inputs and you can prove the two following
  lemmas.
 *)
Fixpoint cmd_seq (c1 c2 : stack_cmd) : stack_cmd :=
  match c1 with
  | cmd_atom v c' => cmd_atom v (cmd_seq c' c2)
  | cmd_unop f c' => cmd_unop f (cmd_seq c' c2)
  | cmd_binop f c' => cmd_binop f (cmd_seq c' c2)
  | cmd_swap n1 n2 c' => cmd_swap n1 n2 (cmd_seq c' c2)
  | cmd_flatmap cf c' => cmd_flatmap cf (cmd_seq c' c2)
  | cmd_reduce cf c' => cmd_reduce cf (cmd_seq c' c2)
  | cmd_skip => c2
  end.

Lemma cmd_seq_wt_helper c1 c2 S1 S2 S3
  : cmd_well_typed S1 c1 S2 ->
    cmd_well_typed S2 c2 S3 ->
    cmd_well_typed S1 (cmd_seq c1 c2) S3.
Proof.
  induct c1; simplify; invert H.
  - apply cmd_atom_wt with (t := t).

    + assumption.
    + apply IHc1 with (S2 := S2); assumption.
  - apply cmd_unop_wt with (t2 := t2).
    + assumption.
    + apply IHc1 with (S2 := S2); assumption.
  - apply cmd_binop_wt with (t3 := t3).
    + assumption.
    + apply IHc1 with (S2 := S2); assumption.
  - apply cmd_swap_wt.
    + assumption.
    + assumption.
    + apply IHc1 with (S2 := S2); assumption.
  - apply cmd_flatmap_wt with (t2 := t2).
    + apply IHc1_2 with (S2 := S2); assumption.
    + assumption.
  - apply cmd_reduce_wt.
    + apply IHc1_2 with (S2 := S2); assumption.
    + assumption.
  - assumption.
Qed.


Lemma cmd_seq_wt S1 S2 S3 c1 c2
  : cmd_well_typed S1 c1 S2 ->
    cmd_well_typed S2 c2 S3 ->
    cmd_well_typed S1 (cmd_seq c1 c2) S3.
Proof.
  apply cmd_seq_wt_helper.
Qed.

Lemma interp_seq c1 c2 s
  : interp_cmd (cmd_seq c1 c2) s
    = interp_cmd c2 (interp_cmd c1 s).
Proof.
  induct c1; simplify.
  - apply IHc1.
  - apply IHc1.
  - apply IHc1.
  - apply IHc1.
  - cases s; simplify; apply IHc1_2.
  - cases s.
    + simplify.
      apply IHc1_2.
    + cases s0; simplify; apply IHc1_2.
  - equality.
Qed.



(*
  Let's take a look at ways to optimize programs in our language.
  You may have noticed in our earlier tests that it's often convenient
  to write `stack_cmd` programs that push constants and immediately
  operate on them, or that perform a couple unops and/or binops in sequence.
  Let's take advantage of the way we defined `stack_cmd` to collapse
  those operations where possible. We'll call this "partial evaluation"
  since we're effectively interpreting portions of our command sequence
  to compute parts of the result ahead of time.

  For example, if we have a `cmd_atom` immediately followed by a
  `cmd_binop`, we want to combine the two into a `cmd_unop` by filling in
  one argument of the `cmd_binop`'s function. Take a look at the tests
  to get a better idea of this function's expected behavior.
 *)
Fixpoint partial_eval c :=
  match c with
  | cmd_atom v c' =>
      match partial_eval c' with
      | cmd_unop f c'' => cmd_atom (f v) c''
      | cmd_binop f c'' => cmd_unop (f v) c''
      | c'_fused => cmd_atom v c'_fused
      end
  | cmd_unop f c' => 
      match partial_eval c' with
      | cmd_unop g c'' => cmd_unop (fun v => g (f v)) c''
      | cmd_binop g c'' => cmd_binop (fun v1 v2 => g (f v1) v2) c''
      | c'_fused => cmd_unop f c'_fused
      end
  | cmd_binop f c' =>
      match partial_eval c' with
      | cmd_unop g c'' => cmd_binop (fun v1 v2 => g (f v1 v2)) c''
      | c'_fused => cmd_binop f c'_fused
      end
  | cmd_swap n1 n2 c' => cmd_swap n1 n2 (partial_eval c')                 
  | cmd_flatmap cf1 c' => cmd_flatmap (partial_eval cf1) (partial_eval c')
  | cmd_reduce cf c' => cmd_reduce (partial_eval cf) (partial_eval c')
  | cmd_skip => cmd_skip
  end.


(* Some common commands for use in our test cases *)
Definition val_add x y :=
  match x,y with
  | val_lit xl, val_lit yl => val_lit (xl + yl)
  | _,_ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Definition val_square x :=
  match x with
  | val_lit xl => val_lit (Nat.square xl)
  | _ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Definition cmd_singleton := cmd_unop (fun x => val_cons x val_nil).
Definition cmd_lit n := cmd_atom (val_lit n).
Definition cmd_cons := cmd_binop val_cons.
Definition cmd_add := cmd_binop val_add.

Lemma partial_eval_test1
  : partial_eval (cmd_atom (val_lit 2) (cmd_unop val_square cmd_skip))
    = (cmd_atom (val_lit 4) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test2
  : partial_eval (cmd_atom (val_lit 5) (cmd_binop val_add cmd_skip))
    = (cmd_unop (val_add (val_lit 5)) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test3
  : partial_eval (cmd_unop val_square (cmd_unop val_square cmd_skip))
    = (cmd_unop (fun v => val_square (val_square v)) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test4
  : partial_eval (cmd_binop val_add (cmd_unop val_square cmd_skip))
    = (cmd_binop (fun v1 v2 => val_square (val_add v1 v2)) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test5
  : partial_eval (cmd_swap 0 2 (cmd_atom (val_lit 2) (cmd_atom (val_lit 3) (cmd_binop val_add cmd_skip))))
    = cmd_swap 0 2 (cmd_atom (val_lit 5) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test6
  : partial_eval (cmd_unop val_square (cmd_atom (val_lit 1) (cmd_binop val_add (cmd_unop val_square cmd_skip))))
    = cmd_unop (fun x => val_square (val_add (val_lit 1) (val_square x))) cmd_skip.
Proof. equality. Qed.

Lemma partial_eval_test7
  : partial_eval (cmd_flatmap (cmd_atom (val_lit 2) (cmd_binop val_add (cmd_singleton cmd_skip)))
               (cmd_atom (val_lit 2) (cmd_unop val_square cmd_skip)))
    = cmd_flatmap (cmd_unop (fun v2 => val_cons (val_add (val_lit 2) v2) val_nil) cmd_skip)
        (cmd_atom (val_lit 4) cmd_skip).
Proof. equality. Qed.

(* With any program transformation, we want to make sure
   that it preserves all the right invariants, the most
   basic of which is type soundness, the idea that,
   given well-formed input, our optimization produces
   well-formed output.

   Since types are the focus of the next assignment,
   we've proven this for you.
 *)
Lemma partial_eval_sound S c S'
  : cmd_well_typed S c S' ->
    cmd_well_typed S (partial_eval c) S'.
Proof.
  induct 1;
    simplify;
    eauto.
  all:cases (partial_eval c);
    simplify;
    eauto.
  all: invert IHcmd_well_typed; eauto.
Qed.



(* 
  Now that we've warmed up, let's get to the meat of this assigment,
  proving compiler correctness. Since we've defined the semantics of
  our language with an interpreter, we want to show that, given an
  arbitrary (well-typed) stack, interpreting the output of our compiler
  will give us the same result as interpreting the input. If you're having
  trouble, make sure to check the hints, as this proof is tricky.

  WARNING: For this assignment in particular, be careful of simplifying
           too early. `simplify` is helpful, but doesn't always do what
           you want when dealing with the cases here. Our solution does
           use `simplify`, but you should specifically be cautious of
           using it after using `cases (partial_eval c)` (which will likely
           appear in your proof).

  If you're having trouble with the function argument to val_flatmap,
  read HINT 4 in Pset6Sig.v.

 *)

Definition partial_atom v c :=
  match c with
  | cmd_atom v0 c0 => cmd_atom v (cmd_atom v0 c0)
  | cmd_unop f c'' => cmd_atom (f v) c''
  | cmd_binop f c'' => cmd_unop (f v) c''
  | cmd_swap n1 n2 c0 => cmd_atom v (cmd_swap n1 n2 c0)
  | cmd_flatmap cf c0 => cmd_atom v (cmd_flatmap cf c0)
  | cmd_reduce cf c0 => cmd_atom v (cmd_reduce cf c0)
  | cmd_skip => cmd_atom v cmd_skip
  end.

Definition partial_unop f c :=
  match c with
  | cmd_atom v c0 => cmd_unop f (cmd_atom v c0)
  | cmd_unop g c'' => cmd_unop (fun v : stack_val => g (f v)) c''
  | cmd_binop g c'' => cmd_binop (fun v1 v2 : stack_val => g (f v1) v2) c''
  | cmd_swap n1 n2 c0 => cmd_unop f (cmd_swap n1 n2 c0)
  | cmd_flatmap cf c0 => cmd_unop f (cmd_flatmap cf c0)
  | cmd_reduce cf c0 => cmd_unop f (cmd_reduce cf c0)
  | cmd_skip => cmd_unop f cmd_skip
  end.

Definition partial_binop f c :=
  match c with
  | cmd_atom v c0 => cmd_binop f (cmd_atom v c0)
  | cmd_unop g c'' => cmd_binop (fun v1 v2 : stack_val => g (f v1 v2)) c''
  | cmd_binop f0 c0 => cmd_binop f (cmd_binop f0 c0)
  | cmd_swap n1 n2 c0 => cmd_binop f (cmd_swap n1 n2 c0)
  | cmd_flatmap cf c0 => cmd_binop f (cmd_flatmap cf c0)
  | cmd_reduce cf c0 => cmd_binop f (cmd_reduce cf c0)
  | cmd_skip => cmd_binop f cmd_skip
  end.

Lemma partial_atom_correct c S S' v :
    cmd_well_typed S (cmd_atom v c) S' ->
    forall s, stack_well_typed s S ->
    interp_cmd (cmd_atom v c) s = interp_cmd (partial_atom v c) s.
Proof.
  cases c; auto.
  simplify.
  cases s; auto.
  invert H.
  invert H6.
  invert H0.
Qed.

Lemma partial_unop_correct c S S' f :
    cmd_well_typed S (cmd_unop f c) S' ->
    forall s, stack_well_typed s S ->
    interp_cmd (cmd_unop f c) s = interp_cmd (partial_unop f c) s.
Proof.
  cases c; auto; simplify; cases s; auto.
  simplify.
  cases s0; auto.
  invert H.
  invert H6.
  invert H0.
  invert H6.
Qed.

Lemma partial_binop_correct c S S' f :
    cmd_well_typed S (cmd_binop f c) S' ->
    forall s, stack_well_typed s S ->
    interp_cmd (cmd_binop f c) s = interp_cmd (partial_binop f c) s.
Proof.
  cases c; auto.
  simplify.
  cases s; auto.
  cases s0; auto.
  invert H.
  invert H0.
  invert H7.
Qed.

Lemma partial_eval_correct_helper c S S'
  : cmd_well_typed S c S' ->
    forall s, stack_well_typed s S -> interp_cmd (partial_eval c) s = interp_cmd c s.
Proof.
  induct c.
  - pose (partial_atom_correct (partial_eval c) S S' v).
    unfold partial_atom in e.
    simplify.
    invert H.
    rewrite <- e.
    + apply IHc with (S := t :: S) (S' := S').
      * assumption.
      * apply Forall2_cons; assumption.
    + apply cmd_atom_wt with (t := t).
      * assumption.
      * apply partial_eval_sound.
        assumption.
    + assumption.
  - pose (partial_unop_correct (partial_eval c) S S' f).
    unfold partial_unop in e.
    simplify.
    invert H.
    invert H0.
    rewrite <- e.
    + apply IHc with (S := t2 :: S0) (S' := S').
      * assumption.
      * simplify.
        apply Forall2_cons.
        -- apply H4.
           assumption.
        -- assumption.
    + apply cmd_unop_wt with (t2 := t2).
      * assumption.
      * apply partial_eval_sound.
        assumption.
    + apply Forall2_cons; assumption.
  - pose (partial_binop_correct (partial_eval c) S S' f).
    unfold partial_binop in e.
    simplify.
    invert H.
    invert H0.
    invert H5.
    rewrite <- e.
    + apply IHc with (S := t3 :: S0) (S' := S').
      * assumption.
      * simplify.
        apply Forall2_cons.
        -- apply H4;
            assumption.
        -- assumption.
    + apply cmd_binop_wt with (t3 := t3).
      * assumption.
      * apply partial_eval_sound.
        assumption.
    + apply Forall2_cons.
      * assumption.
      * apply Forall2_cons; assumption.
  - simplify.
    invert H.
    apply IHc with (S := swap n1 n2 S) (S' := S').
    + assumption.
    + apply Forall2_swap.
      assumption.
  - simplify.
    invert H.
    invert H0.
    simplify.
    rewrite val_flatmap_same with (t := t1) (g := (fun x0 : stack_val => stack_peek (interp_cmd c1 [x0]))).
    + apply IHc2 with (S := ty_list t2 :: S0) (S' := S').
      * assumption.
      * apply Forall2_cons.
        -- apply val_flatmap_sound with (t1 := t1).
           ++ simplify.
              apply stack_peek_sound with (S := []).
              apply interp_sound with (S := [t1]).
              ** assumption.
              ** apply Forall2_cons; auto.
           ++ assumption.
        -- assumption.
    + simplify.
      rewrite IHc1 with (S := [t1]) (S' := [ty_list t2]).
      * equality.
      * assumption.
      * apply Forall2_cons; auto.
    + assumption.
  - simplify.
    invert H.
    invert H0.
    invert H5.
    simplify.
    rewrite val_reduce_same with (t := t) (tacc := t_acc) (g := (fun acc x1 : stack_val => stack_peek (interp_cmd c1 [x1; acc]))).
    + apply IHc2 with (S := t_acc :: S0) (S' := S').
      * assumption.
      * apply Forall2_cons.
        -- apply val_reduce_sound with (t := t).
           ++ simplify.
              apply stack_peek_sound with (S := []).
              apply interp_sound with (S := [t; t_acc]).
              ** assumption.
              ** apply Forall2_cons; auto.
           ++ assumption.
           ++ assumption.
        -- assumption.
    + simplify.
      rewrite IHc1 with (S := [t; t_acc]) (S' := [t_acc]).
      * apply stack_peek_sound with (S := []).
        apply interp_sound with (S := [t; t_acc]).
        -- assumption.
        -- apply Forall2_cons; auto.
      * equality.
      * apply Forall2_cons; auto.
    + simplify.
      apply stack_peek_sound with (S := []).
        apply interp_sound with (S := [t; t_acc]).
        -- assumption.
        -- apply Forall2_cons; auto.
    + simplify.
      rewrite IHc1 with (S := [t; t_acc]) (S' := [t_acc]); auto.
    + assumption.
    + assumption.
  - simplify.
    equality.
Qed.

Lemma partial_eval_correct S c S'
  : cmd_well_typed S c S' ->
    forall s, stack_well_typed s S -> interp_cmd (partial_eval c) s = interp_cmd c s.
Proof.
  apply partial_eval_correct_helper.
Qed.


(*
  Let's try another compiler optimization. It turns out that when we have
  two flatmap commands in a row, we can reorder them so that the second
  one operates on each output of the first as it's produced. In other
  words, instead of generating a whole intermediate list, we can compute
  the final output as we calculate each intermediate element. This idea
  is from a family of optimizations called list fusion.

  The following lemma formalizes this idea.

  
  If you're having trouble with the function argument to val_flatmap,
  read HINT 2 in Pset6Sig.v.
 *)

Lemma flatmap_same f g l:
  (forall x, f x = g x) ->
  val_flatmap f l = val_flatmap g l.
Proof.
  induct l; auto; simplify.
    rewrite H.
    rewrite IHl2; auto.
Qed.

Lemma app_assoc v1 v2 v3:
    val_app v1 (val_app v2 v3)
    = val_app (val_app v1 v2) v3.
Proof.
  induct v1; auto.
  simplify.
  rewrite IHv1_2.
  equality.
Qed.

Lemma flatmap_app f v1 v2:
    val_flatmap f (val_app v1 v2)
    = val_app (val_flatmap f v1) (val_flatmap f v2).
Proof.
  induct v1; auto.
  simplify.
  rewrite IHv1_2.
  rewrite app_assoc.
  equality.
Qed.

Lemma flatmap_fuse_helper f g v: 
    val_flatmap f (val_flatmap g v)
    = val_flatmap (fun x => val_flatmap f (g x)) v.
Proof.
  induct v; auto.
  simplify.
  rewrite flatmap_app.
  rewrite IHv2.
  equality.
Qed.

Lemma flatmap_fuse : forall cf1 cf2 c s,
    interp_cmd (cmd_flatmap cf1 (cmd_flatmap cf2 c)) s
    = interp_cmd (cmd_flatmap (cmd_seq cf1 (cmd_flatmap cf2 cmd_skip)) c) s.
Proof.
  simplify.
  cases s; auto.
  simplify.
  rewrite flatmap_fuse_helper.
  rewrite flatmap_same with (g := (fun x : stack_val => stack_peek (interp_cmd (cmd_seq cf1 (cmd_flatmap cf2 cmd_skip)) [x]))).
  - equality.
  - simplify.
    rewrite interp_seq.
    simplify.
    cases (interp_cmd cf1 [x]); auto.
Qed.


(*
  Now, define an optimization pass that does this transformation on an
  arbitrary input command. Try to fuse as many instances of consecutive
  flatmaps as you can. You don't have to catch everything (there is one
  specific corner case that is difficult). For full credit, you should
  pass all of the test cases below without hardcoding them. If your
  definition isn't passing all of the test cases, try to compare it to
  our `partial_eval` compiler earlier and see if you're missing out on any
  chances to optimize.

  If you're having trouble with the tests, read HINT 3 in Pset6Sig.v.
 *)
Fixpoint loop_fuse (c : stack_cmd) : stack_cmd :=
  match c with
  | cmd_atom v c' => cmd_atom v (loop_fuse c')
  | cmd_unop f c' => cmd_unop f (loop_fuse c')
  | cmd_binop f c' => cmd_binop f (loop_fuse c')
  | cmd_swap n1 n2 c' => cmd_swap n1 n2 (loop_fuse c')                 
  | cmd_flatmap cf1 c' =>
    match loop_fuse c' with
      | cmd_flatmap cf2 c'' => cmd_flatmap (cmd_seq (loop_fuse cf1) (cmd_flatmap cf2 cmd_skip)) c''
      | c'_fused => cmd_flatmap (loop_fuse cf1) c'_fused
    end
  | cmd_reduce cf c' => cmd_reduce cf (loop_fuse c')
  | cmd_skip => cmd_skip
  end.

(*
  Your loop_fuse optimizer should pass all of the following tests.
  In the event that your optimizer fuses more `cmd_flatmap`s than ours
  and this causes one or more of these tests to fail, admit the failing test,
  add a corresponding passing test, and explain why the second output is superior.
 *)

Lemma loop_fuse_test1
  : loop_fuse (cmd_flatmap (cmd_singleton (cmd_lit 0 (cmd_cons cmd_skip)))
                 (cmd_flatmap (cmd_lit 1 (cmd_add (cmd_singleton cmd_skip))) cmd_skip))
    = (cmd_flatmap (cmd_singleton
                      (cmd_lit 0
                         (cmd_cons
                            (cmd_flatmap (cmd_lit 1 (cmd_add (cmd_singleton cmd_skip)))
                               cmd_skip))))
         cmd_skip).
Proof. equality. Qed.

Lemma loop_fuse_test2
  : loop_fuse (cmd_flatmap (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                              (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                                 (cmd_singleton cmd_skip)))
                 cmd_skip)
    = cmd_flatmap
         (cmd_flatmap
            (cmd_unop val_square
               (cmd_singleton
                  (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                     cmd_skip)))
            (cmd_singleton cmd_skip))
         cmd_skip.
Proof. equality. Qed.


Lemma loop_fuse_test3
  : loop_fuse (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                 (cmd_flatmap (cmd_singleton (cmd_lit 0 (cmd_cons cmd_skip)))
                 (cmd_flatmap (cmd_lit 1 (cmd_add (cmd_singleton cmd_skip))) cmd_skip)))
    = cmd_flatmap
        (cmd_unop val_square
           (cmd_singleton
              (cmd_flatmap
                 (cmd_singleton
                    (cmd_atom (val_lit 0)
                       (cmd_binop val_cons
                          (cmd_flatmap
                             (cmd_atom (val_lit 1)
                                (cmd_binop val_add (cmd_singleton cmd_skip)))
                             cmd_skip))))
                 cmd_skip)))
        cmd_skip.
Proof. equality. Qed.


(* As a first step, let's prove that this optimization preserves
   our typing judgment like before. The proof will be very similar
   to the one for `op_fuse`.
 *)
Lemma loop_fuse_sound S c S'
  : cmd_well_typed S c S' ->
    cmd_well_typed S (loop_fuse c) S'.
Proof.
  induct 1; simplify.
  - apply cmd_atom_wt with (t := t); assumption.
  - apply cmd_unop_wt with (t2 := t2); assumption.
  - apply cmd_binop_wt with (t3 := t3); assumption.
  - apply cmd_swap_wt; assumption.
  - cases (loop_fuse c).
    + apply cmd_flatmap_wt with (t2 := t2); assumption.
    + apply cmd_flatmap_wt with (t2 := t2); assumption.
    + apply cmd_flatmap_wt with (t2 := t2); assumption.
    + apply cmd_flatmap_wt with (t2 := t2); assumption.
    + invert IHcmd_well_typed1.
      apply cmd_flatmap_wt with (t2 := t3); auto.
      apply cmd_seq_wt with (S2 := [ty_list t2]); auto.
      apply cmd_flatmap_wt with (t2 := t3); auto.
    + apply cmd_flatmap_wt with (t2 := t2); assumption.
    + apply cmd_flatmap_wt with (t2 := t2); assumption.
  - apply cmd_reduce_wt; assumption.
  - apply cmd_skip_wt.
Qed.


(*
  Now for the largest proof of the pset, let's prove that `loop_fuse` is correct.
  Make sure you've attempted `op_fuse_correct` first since the proof is similar
  and relies on some of the same lemmas.
 *)
Lemma loop_fuse_correct S c S'
  : cmd_well_typed S c S' ->
    forall s, stack_well_typed s S -> interp_cmd (loop_fuse c) s = interp_cmd c s.
Proof.
  induct 1; simplify; auto.
  - rewrite IHcmd_well_typed; auto.
    invert H1.
    simplify.
    auto.
  - rewrite IHcmd_well_typed; auto.
    invert H1.
    invert H6.
    simplify.
    auto.
  - cases (loop_fuse c).
    + rewrite <- Heq in *.
      invert H1.
      simplify.
      rewrite IHcmd_well_typed1.
      * rewrite val_flatmap_same with (t := t1) (g := (fun x0 : stack_val => stack_peek (interp_cmd cf [x0]))); auto.
        simplify.
        rewrite IHcmd_well_typed2; auto.
      * apply Forall2_cons; auto.
        apply val_flatmap_sound with (t1 := t1); auto.
        simplify.
        apply stack_peek_sound with (S := []).
        apply interp_sound with (S := [t1]); auto.
        apply loop_fuse_sound.
        assumption.
    + rewrite <- Heq in *.
      invert H1.
      simplify.
      rewrite IHcmd_well_typed1.
      * rewrite val_flatmap_same with (t := t1) (g := (fun x0 : stack_val => stack_peek (interp_cmd cf [x0]))); auto.
        simplify.
        rewrite IHcmd_well_typed2; auto.
      * apply Forall2_cons; auto.
        apply val_flatmap_sound with (t1 := t1); auto.
        simplify.
        apply stack_peek_sound with (S := []).
        apply interp_sound with (S := [t1]); auto.
        apply loop_fuse_sound.
        assumption.
    + rewrite <- Heq in *.
      invert H1.
      simplify.
      rewrite IHcmd_well_typed1.
      * rewrite val_flatmap_same with (t := t1) (g := (fun x0 : stack_val => stack_peek (interp_cmd cf [x0]))); auto.
        simplify.
        rewrite IHcmd_well_typed2; auto.
      * apply Forall2_cons; auto.
        apply val_flatmap_sound with (t1 := t1); auto.
        simplify.
        apply stack_peek_sound with (S := []).
        apply interp_sound with (S := [t1]); auto.
        apply loop_fuse_sound.
        assumption.
    + rewrite <- Heq in *.
      invert H1.
      simplify.
      rewrite IHcmd_well_typed1.
      * rewrite val_flatmap_same with (t := t1) (g := (fun x0 : stack_val => stack_peek (interp_cmd cf [x0]))); auto.
        simplify.
        rewrite IHcmd_well_typed2; auto.
      * apply Forall2_cons; auto.
        apply val_flatmap_sound with (t1 := t1); auto.
        simplify.
        apply stack_peek_sound with (S := []).
        apply interp_sound with (S := [t1]); auto.
        apply loop_fuse_sound.
        assumption.
    + rewrite <- flatmap_fuse.
      rewrite <- Heq in *.
      invert H1.
      simplify.
      rewrite IHcmd_well_typed1.
      * rewrite val_flatmap_same with (t := t1) (g := (fun x0 : stack_val => stack_peek (interp_cmd cf [x0]))); auto.
        simplify.
        rewrite IHcmd_well_typed2; auto.
      * apply Forall2_cons; auto.
        apply val_flatmap_sound with (t1 := t1); auto.
        simplify.
        apply stack_peek_sound with (S := []).
        apply interp_sound with (S := [t1]); auto.
        apply loop_fuse_sound.
        assumption.
    + rewrite <- Heq in *.
      invert H1.
      simplify.
      rewrite IHcmd_well_typed1.
      * rewrite val_flatmap_same with (t := t1) (g := (fun x0 : stack_val => stack_peek (interp_cmd cf [x0]))); auto.
        simplify.
        rewrite IHcmd_well_typed2; auto.
      * apply Forall2_cons; auto.
        apply val_flatmap_sound with (t1 := t1); auto.
        simplify.
        apply stack_peek_sound with (S := []).
        apply interp_sound with (S := [t1]); auto.
        apply loop_fuse_sound.
        assumption.
    + rewrite <- Heq in *.
      invert H1.
      simplify.
      rewrite IHcmd_well_typed1.
      * rewrite val_flatmap_same with (t := t1) (g := (fun x0 : stack_val => stack_peek (interp_cmd cf [x0]))); auto.
        simplify.
        rewrite IHcmd_well_typed2; auto.
      * apply Forall2_cons; auto.
        apply val_flatmap_sound with (t1 := t1); auto.
        simplify.
        apply stack_peek_sound with (S := []).
        apply interp_sound with (S := [t1]); auto.
        apply loop_fuse_sound.
        assumption.
  - invert H1.
    invert H6.
    simplify.
    rewrite IHcmd_well_typed1; auto.
    apply Forall2_cons; auto.
    apply val_reduce_sound with (t := t); auto.
    simplify.
    apply stack_peek_sound with (S := []).
    apply interp_sound with (S := [t; t_acc]); auto.
Qed.



End Impl.

Module ImplCorrect : Pset6Sig.S := Impl.

(* Authors: Dustin Jamner *)
