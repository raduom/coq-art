(* From: https://matthew.brecknell.net/post/pattern-matching-dependent-types-in-coq/ *)

Definition admit {T: Set}: T. Admitted.

Inductive vec (A: Set): nat -> Set :=
| nil  : vec A 0
| cons : forall n, A -> vec A n -> vec A (S n).

Arguments nil  {A}.
Arguments cons {A n} _ _.
Notation "::" := cons.

(* nat_disc *)
Definition nat_disc {T: Set} {n: nat} (H: S n = 0): T.
  refine (
      match H in _ = j return
            match j with
            | O => T
            | S i => unit
            end
      with
      | eq_refl => tt
      end
    ).
Defined.

(* succ_rewrite *)
Definition succ_rewrite {T: nat -> Set} {p q: nat} (H: S p = S q): T q -> T p.
  refine (
      match H in _ = j return
            match j with
            | O   => unit
            | S i => T i -> T p
            end
      with
      | eq_refl => fun t => t
      end
    ).
Defined.

Definition zip' {A B C: Set} (f: A -> B -> C):
  forall n, vec A n -> vec B n -> vec C n.
  refine (
      fix zip {n} xs :=
        match xs in vec _ j return vec B j -> vec C j with
        | nil => fun ys => nil
        | @cons _ p x xt => fun ys =>
          match ys in vec _ j return S p = j -> vec C (S p) with
          | nil => nat_disc
          | @cons _ q y yt => fun Heq => cons (f x y) (zip xt (succ_rewrite Heq yt))
          end eq_refl
        end
    ).
Defined.

Definition uncons {A: Set} {n: nat} (v: vec A (S n)): A * vec A n.
  refine (
      match v in vec _ j return
            match j with
            | O => unit
            | S i => A * vec A i
            end
      with
      | nil => tt
      | @cons _ p x xt => (x, xt)
      end
    ).
Defined.

Definition zip {A B C: Set} (f: A -> B -> C):
  forall n, vec A n -> vec B n -> vec C n.
  refine (
      fix zip {n}: vec A n -> vec B n -> vec C n :=
        match n as p return vec A p -> vec B p -> vec C p with
        | O   => fun xs ys => nil
        | S i => fun xs ys =>
                  match uncons xs, uncons ys with
                  | (x, xt), (y, yt) =>
                    cons (f x y) (zip xt yt)
                  end
        end
    ).
Defined.