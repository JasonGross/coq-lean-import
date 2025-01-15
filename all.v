From Coq Require Import Bool.
From Coq Require Import Arith.
Module SF.
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).
Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).
Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BNeq a1 a2 => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BGt a1 a2 => negb ((aeval a1) <=? (aeval a2))
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.
End SF.


From LeanImport Require Import Lean.
Lean Import "./all.out".
(* Print aexp.
Print aeval. *)
(* Goal True.
pose aeval as T.
unfold aeval in T.
Show. *)
Record ISO (A B : Type) :=
  {
    to : A -> B;
    from : B -> A;
    to_from : forall a, from (to a) = a;
    from_to : forall b, to (from b) = b;
  }.

Print nat. (* Inductive nat : Set := O : nat | S : nat -> nat. *)
Print Nat. (* Inductive Nat : Type := Nat_zero : Nat | Nat_succ : Nat -> Nat. *)

Goal ISO nat Nat.
Proof.
  (* We will build the record by providing the 'to' and 'from' functions,
     then prove their round-trip correctness. *)
  pose (fix f (n : nat) :=
              match n with
              | O    => Nat_zero
              | S n' => Nat_succ (f n')
              end) as f.
  pose (fix g (m : Nat) :=
                match m with
                | Nat_zero    => O
                | Nat_succ m' => S (g m')
                end) as g.
              
  refine (
    {|
      to := f;

      from := g
    |}
  ).
  - (* to_from: from (to a) = a *)
    refine (fun a => _).
    induction a; simpl.
    + reflexivity.
    + f_equal. apply IHa.
  - (* from_to: to (from b) = b *)
    intro b.
    induction b; simpl.
    + reflexivity.
    + f_equal. apply IHb.
Qed.

