Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export ZArithRing.

(* Exercise 5.1, too simple *)

(* Exercise 5.2 *)
Theorem all_perm : forall (A: Type) (P: A -> A -> Prop), (forall x y: A, P x y) -> forall x y: A, P y x.
Proof.
  intros A P Hp x y; apply (Hp y x).
Qed.

Print all_perm.

Theorem resolution :
  forall (A:Type) (P Q R S: A -> Prop), (forall a:A, Q a -> R a -> S a) -> (forall b:A, P b -> Q b) -> (forall c:A, P c -> R c -> S c).
Proof.
  intros A P Q R S Hqrs Hpq c Hp Hr.
  apply Hqrs; [apply Hpq | idtac]; assumption.
Qed.

(* Exercise 5.3 *)

Theorem modus_ponens : forall P Q:Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q p Hp; apply Hp; assumption.
Qed.

Lemma ex_5_3_1 : ~False.
Proof.
  intros Hf. elim Hf.
Qed.

(* double negation elimination *)
Lemma ex_5_3_2 : forall P: Prop, ~~~P -> ~P.
Proof.
  intros P Hp Cp. unfold not in Hp.
  apply Hp. intros Hp0. apply Hp0.
  assumption.
Qed.

(* did not use elim *)
Lemma ex_5_3_3 : forall P Q: Prop, (P -> Q) -> ~Q -> ~P.
Proof.
  intros P Q Hpq Cp Hq.
  apply Cp; apply Hpq; assumption.
Qed.

(* for some reason i cannot use the absurd thm *)
Lemma ex_5_3_4 : forall P Q R: Prop, (P -> Q) -> (P -> ~Q) -> P -> R.
Proof.
  unfold not; intros P Q R Hpq Hpnq Hp.
  elim Hpnq; [assumption | apply Hpq; assumption].
Qed.

(* Exercise 5.4 *)

(* Definition dyslexic_contrap : forall P Q: Prop, (P -> Q) -> (~P -> ~Q). *)

Theorem dys_imp_f :
  (forall P Q: Prop, (P -> Q) -> (Q -> P)) -> False.
Proof.
  intros Hd; apply (Hd False True);
    [intros C; elim C | apply I].
Qed.

Theorem dys_contrap_f :
  (forall P Q: Prop, (P -> Q) -> (~P -> ~Q)) -> False.
Proof.
  intros Hc; apply (Hc False True);
    try (intros C; elim C); apply I.
Qed.

(* Exercise 5.5 *)

Theorem ex_5_5 : forall (A: Set) (a b c d: A), a=c \/ b=c \/ c=c \/ d=c.
Proof.
  intros A a b c d;
    right; right; left; reflexivity.
Qed.

(* Exercise 5.6 *)

Lemma ex_5_6_1 :
  forall A B C: Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C H.
  destruct H as [Ha [Hb Hc]];
  repeat split; assumption.
Qed.

Lemma ex_5_6_2 :
  forall A B C D: Prop, (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D.
Proof.
  intros A B C D [Hab [Hcd [Ha Hc]]]; split;
    [apply Hab | apply Hcd]; assumption.
Qed.

Lemma ex_5_6_3 :
  forall A: Prop, ~(A /\ ~A).
Proof.
  intros A [C1 C2]; apply C2; assumption.
Qed.

Lemma ex_5_6_4 :
  forall A B C: Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C [Ha | [Hb | Hc]];
    [ left; left | left; right | right ];
    assumption.
Qed.

Lemma ex_5_6_5 :
  forall A: Prop, ~~(A \/ ~A).
Proof.
  unfold not;
    intros A C; apply C; right; intros Ha;
      apply C; left; assumption.
Qed.

Lemma ex_5_6_6 :
  forall A B: Prop, (A \/ B) /\ ~A -> B.
Proof.
  intros A B [[Ha | Hb] Ca];
    [elim Ca | idtac ]; assumption.
Qed.

(* Exercise 5.7 *)

Definition peirce := forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition classic := forall P: Prop, ~~P -> P.
Definition excluded_middle := forall P: Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q: Prop, ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q: Prop, (P -> Q) -> (~P \/ Q).

Lemma ex_5_7_1:
  peirce -> classic.
Proof.
  unfold peirce, classic, not; intros H P Hp.
  apply (H P False). intros H0; elim Hp; assumption.
Qed.

Lemma ex_5_7_2:
  classic -> excluded_middle.
Proof.
  unfold classic, excluded_middle; intros H P;
    apply H; intros H0.
  absurd P.
  - intros Hp; apply H0; now left.
  - apply H; intros Cp; apply H0; now right.
Qed.

Lemma ex_5_7_3:
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle, de_morgan_not_and_not.
  intros H P Q Hpq.
  destruct (H P) as [Hp | Cp];
    destruct (H Q) as [Hq | Cq];
    [ left | left | right | elim Hpq; split ];
    assumption.
Qed.

Lemma pp: forall P: Prop, P -> P.
Proof.
  (intros P Hp; assumption). Qed.

Lemma ex_5_7_4':
  de_morgan_not_and_not -> classic.
Proof.
  unfold de_morgan_not_and_not, classic.
  intros H P Cp.
  apply or_ind with (A:=P) (B:=P);
    [apply pp | apply pp | idtac].
  apply H; intros [Hc _].
  apply Cp; assumption.
Qed.

Lemma ex_5_7_4:
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not, implies_to_or;
    intros Hm P Q Hpq.
  apply Hm; intros [Cp Cq].
  apply Cq. apply Hpq.
  apply ex_5_7_4';
    [intros | idtac]; assumption.
Qed.

Lemma ex_5_7_5:
  implies_to_or -> peirce.
Proof.
  unfold implies_to_or, peirce;
    intros Hpq P Q H.
  assert (Hc: ~P \/ P) by (apply Hpq; now intros Hp).
  destruct Hc.
  - apply H; intros Hp; elim (H0 Hp).
  - assumption.
Qed.

(* Exercise 5.9 *)

Section Ex_5_9.
  Variable A:Set.
  Variables P Q: A -> Prop.

  Theorem ex_5_9_1:
    (exists x: A, P x \/ Q x) -> (ex P) \/ (ex Q).
  Proof.
    intros H; elim H; clear H; intros x [H | H];
      [left | right]; now exists x.
  Qed.

  Theorem ex_5_9_2:
    (ex P) \/ (ex Q) -> exists x: A, P x \/ Q x.
  Proof.
    intros [H | H];
      elim H; clear H; intros x H;
    exists x; [left | right]; assumption.
  Qed.

  Theorem ex_5_9_3:
    (exists x: A, (forall R: A -> Prop, R x)) -> 2 = 3.
  Proof.
    intros H; elim H; clear H; intros a Hr.
    elim (Hr (fun _ => False)).
  Qed.

  Theorem ex_5_9_4:
    (forall x:A, P x) -> ~(exists y: A, ~ P y).
  Proof.
    intros H Hy; elim Hy; clear Hy; intros y Hy.
    elim (Hy (H y)).
  Qed.

End Ex_5_9.

(* Exercise 5.10 *)

Theorem plus_permute2:
  forall n m p: nat, n + m + p = n + p + m.
Proof.
  intros n m p.
  rewrite <- plus_assoc.
  pattern (m + p).
  rewrite plus_comm.
  rewrite plus_assoc.
  reflexivity.
Qed.

(* Exercise 5.11 *)

Theorem eq_trans:
  forall (A: Type) (x y z: A), x = y -> y = z -> x = z.
Proof.
  intros A x y z Hxy Hyz.
  apply eq_ind with (x:=y);
    assumption.
  Restart.
  intros A x y z Hxy Hyz.
  rewrite Hxy, Hyz.
  reflexivity.
Qed.

Module Impredicative.
  Definition mTrue : Prop := forall P: Prop, P -> P.
  Definition mFalse : Prop := forall P: Prop, P.

  Theorem mFalse_ind : forall P: Prop, mFalse -> P.
  Proof. intros P Hf; apply Hf. Qed.

  (* Exercise 5.12 *)

  Theorem myI : mTrue.
  Proof (fun P p => p). 

  Theorem mFalse_ind' : forall P: Prop, mFalse -> P.
  Proof (fun P Hf => Hf P).

  (* Exercise 5.13 *)
  Definition mNot (P: Prop): Prop := P -> mFalse.

  Lemma ex_5_3_1 : mNot mFalse.
  Proof.
    unfold mNot, mFalse.
    intros Hf P. apply Hf.
  Qed.

End Impredicative.
Export Impredicative.

Section leibniz.
  Set Implicit Arguments.
  Unset Strict Implicit.
  Variable A: Set.

  Definition leibniz (a b: A): Prop := forall P: A -> Prop, P a -> P b.

  Require Import Relations.
  

  Theorem leibniz_sym : symmetric A leibniz.
  Proof.
    unfold symmetric.
    intros x y H.
    now apply H.
  Qed.

  (* Exercise 5.14 *)
  Theorem leibniz_refl: reflexive A leibniz.
  Proof. easy. Qed.

  Theorem leibniz_trans: transitive A leibniz.
  Proof.
    unfold transitive; intros x y z Hxy Hyz;
      apply Hyz; apply Hxy.
  Qed.

  Theorem leibniz_quiv: equiv A leibniz.
  Proof.
    unfold equiv; split;
      [apply leibniz_refl | split;
                            [apply leibniz_trans | apply leibniz_sym]].
  Qed.

  Theorem leibniz_least_reflexive:
    forall R: relation A, reflexive A R -> inclusion A leibniz R.
  Proof.
    intros R Hrefl x y Hl;
      apply Hl; apply Hrefl.
  Qed.

  Theorem leibniz_eq: forall a b: A, leibniz a b -> a = b.
  Proof.
    intros a b Hl;
      apply Hl; reflexivity.
  Qed.

  Theorem eq_leibniz: forall a b: A, a = b -> leibniz a b.
  Proof.
    intros a b He;
      rewrite He; apply leibniz_refl.
  Qed.

  Theorem leibniz_ind:
    forall (x: A) (P: A -> Prop), P x -> forall y: A, leibniz x y -> P y.
  Proof.
    intros x P Hp y Hl;
      now apply Hl.
  Qed.    

  Definition mAnd (P Q: Prop) := forall R: Prop, (P -> Q -> R) -> R.
  Definition mOr  (P Q: Prop) := forall R: Prop, (P -> R) -> (Q -> R) -> R.
  Definition mEx  (A: Set) (P: A -> Prop) := forall R: Prop, (forall x: A, P x -> R) -> R.

  (* Exercise 5.15 *)
  Section ex_5_15.
    Variables P Q R: Prop.
    Variable  PA : A -> Prop.

    Theorem ex_5_15_1: mAnd P Q -> P.
    Proof.
      intros H; apply H; now intros P' Q'.
    Qed.

    Theorem ex_5_15_2: mAnd P Q -> Q.
    Proof.
      intros H; apply H; now intros P' Q'.
    Qed.

    Theorem ex_5_15_3: (P -> Q -> R) -> mAnd P Q -> R.
    Proof.
      intros Hpqr H;
        apply H; apply Hpqr.
    Qed.

    Theorem ex_5_15_4: P -> mOr P Q.
    Proof.
      intros P' p Hp Hq;
        now apply Hp.
    Qed.      

    Theorem ex_5_15_5: Q -> mOr P Q.
    Proof.
      intros Q' p Hp Hq;
        now apply Hq.
    Qed.

    Theorem ex_5_15_6: (P -> R) -> (Q -> R) -> mOr P Q -> R.
    Proof.
      intros Hpr Hqr Hpq;
        apply Hpq; [apply Hpr | apply Hqr].
    Qed.

    Theorem ex_5_15_7: mOr P mFalse -> P.
    Proof.
      intros Hor; apply Hor;
        [trivial | apply mFalse_ind].
    Qed.

    Theorem ex_5_15_8: mOr P Q -> mOr Q P.
    Proof.
      intros Hor P' Hqr Hpr.
      apply Hor; assumption.
    Qed.

    Theorem ex_5_15_9: forall a: A, PA a -> mEx PA.
    Proof.
      intros a H R0 He.
      now apply (He a). 
    Qed.

    Theorem ex_5_15_10:
      mNot (mEx PA) -> forall a: A, mNot (PA a).
    Proof.
      intros H a Hpa;
        unfold mNot, mEx in *.
      apply H; clear H; intros R0 Hr.
      now apply (Hr a).
    Qed.
  End ex_5_15.

  Definition mLe (n p: nat) :=
    forall P: nat -> Prop, P n -> (forall q: nat, P q -> P (S q)) -> P p.

  (* Exercise 5.16 *)

  Lemma my_le_n: forall n: nat, mLe n n.
  Proof.
    now intros n P Hn Hq.
  Qed.

  Lemma my_le_S:
    forall n p: nat, mLe n p -> mLe n (S p).
  Proof.
    intros n p Hnp P Hrefl Hind.
    apply Hnp.
    - apply Hind; assumption.
    - intros q; apply (Hind (S q)).
  Qed.

  Lemma my_le_le: forall n p: nat, mLe n p -> n <= p.
  Proof.
    unfold mLe; intros n p Hle.
    apply Hle;
      [apply le_refl | apply le_S].
  Qed.

Unset Implicit Arguments.
End leibniz.