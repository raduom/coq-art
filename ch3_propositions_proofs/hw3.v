Require Export ZArith  List  Arith Bool.

Section Minimal_propositional_logic.
  Variables P Q R T : Prop.

(* Exercise 3.2 *)

Lemma idP : P -> P.
Proof.
  intro p; assumption.
Qed.

Lemma idPP : (P -> P) -> (P -> P).
Proof.
  intros _ p; assumption.
Qed.

Lemma imp_trans: (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros Hpq Hqr p; apply Hqr; apply Hpq; assumption.
Qed.

Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros Hpqr q p; apply Hpqr; assumption.
Qed.

Lemma ignore_Q : (P -> R) -> P -> Q -> R.
Proof.
  intros Hpr p q; apply Hpr; assumption.
Qed.

Lemma delta_imp : (P -> P -> Q) -> P -> Q.
Proof.
  intros Hpr p; apply Hpr;  assumption.
Qed.

Lemma delta_impR : (P -> Q) -> (P -> P -> Q).
Proof.
  intros Hpq p _; apply Hpq; assumption.
Qed.

Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  intros Hpq Hpr Hqrt p; apply Hqrt; [apply Hpq | apply Hpr]; assumption.
Qed.

Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros H0; apply H0.
  intros H1; apply H1.
  intros p ; apply H0.
  intros H2. assumption.
Qed.

(* Exercise 3.4 -- needs paper *)

(* Exercise 3.5 *)

Section section_for_cut_example.
  Hypotheses (H: P -> Q)
             (H0: Q -> R)
             (H1: (P -> R) -> T -> Q)
             (H2: (P -> R) -> T).

  Theorem cut_example : Q.
  Proof.
    cut (P -> R).
    intro H3.
    apply H1; [assumption | apply H2; assumption].
    intro p ; apply H0; apply H; assumption.
  Qed.

  Theorem cut_example' : Q.
  Proof.
    apply H1; [intro p; apply H0; apply H; assumption | idtac].
    apply H2; intro p; apply H0; apply H; assumption.
  Qed.

  Print cut_example.
  Print cut_example'.

(*
cut_example = 
let H3 : P -> R := fun p : P => H0 (H p) in (fun H4 : P -> R => H1 H4 (H2 H4)) H3
     : Q

cut_example' = H1 (fun p : P => H0 (H p)) (H2 (fun p : P => H0 (H p)))
     : Q
*)

End section_for_cut_example.


End Minimal_propositional_logic.
