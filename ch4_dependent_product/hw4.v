Require Export ZArith  List  Arith Bool.

(* Exercise 4.2
   A:nat
 *)

Section A_declared.
  Variables (A : Set)
            (P Q : A -> Prop)
            (R : A -> A -> Prop).

  Theorem all_perm : (forall a b : A, R a b) -> forall a b: A, R b a.
  Proof.
    intros H a b. apply (H b a).
  Qed.

  Theorem all_imp_dist :
    (forall a:A, P a -> Q a) -> (forall a:A, P a) -> forall a:A, Q a.
  Proof.
    intros Hpq Hp a; apply Hpq; apply Hp.
  Qed.

  Theorem all_delta : (forall a b: A, R a b) -> forall a:A, R a a.
  Proof.
    intros H a; apply (H a a).
  Qed.

End A_declared.

(* Exercise 4.4 *)

Definition id : forall (A:Set), A -> A := fun _ a => a.

Definition diag : forall A B : Set, (A -> A -> B) -> A -> B :=
  fun _ _ faab a => faab a a.

Definition permute : forall A B C : Set, (A -> B -> C) -> B -> A -> C :=
  fun _ _ _ fabc b a => fabc a b.

Search "to_Z".

Definition f_nat_Z : forall A: Set, (nat -> A) -> Z -> A :=
  fun _ fna z => fna (Z.to_nat z).

(* Exercise 4.5 *)

Theorem all_perm' : forall (A: Type) (P: A -> A -> Prop), (forall x y: A, P x y) -> forall x y: A, P y x.
Proof (fun _ _ Hp x y => Hp y x). 

Theorem resolution' :
  forall (A:Type) (P Q R S: A -> Prop), (forall a:A, Q a -> R a -> S a) -> (forall b:A, P b -> Q b) -> (forall c:A, P c -> R c -> S c).
Proof (fun _ _ _ _ _ Hqrs Hpq c Hp Hr => Hqrs c (Hpq c Hp) Hr).

Theorem resolution'' :
  forall (A:Type) (P Q R S: A -> Prop), (forall a:A, Q a -> R a -> S a) -> (forall b:A, P b -> Q b) -> (forall c:A, P c -> R c -> S c).
Proof.
  intros A P Q R S Hqrs Hpq c Hp Hr.
  apply (Hqrs c); try apply (Hpq c); assumption.
Qed.

Print resolution''.