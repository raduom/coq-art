Require Export ZArith.
Require Export List.
Require Export Arith.
Require Export ZArithRing.

(* Exercise 6.3 *)

Theorem bool_equal: forall b: bool, b = true \/ b = false.
Proof.
  intro b; elim b; [left | right]; reflexivity.
Qed.

Definition bool_equal': forall b: bool, b = true \/ b = false :=
  bool_ind (fun b0: bool => b0 = true \/ b0 = false)
           (or_introl eq_refl)
           (or_intror eq_refl).

(* Exercise 6.6 *)
Definition bool_or (a b: bool): bool :=
  match a with
  | true => true
  | _ => b
  end.

Definition bool_and (a b: bool): bool :=
  match a with
  | true => b
  | _ => false
  end.

Definition bool_not (a: bool): bool :=
  match a with
  | true => false
  | false => true
  end.

Definition bool_eq (a b: bool): bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

Definition bool_xor (a b: bool): bool :=
  bool_not (bool_eq a b).

Theorem ex_6_6_1a:
  forall b1 b2: bool, bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof.
  unfold bool_xor; intros b1 b2; pattern b1; apply bool_ind;
    pattern b2; apply bool_ind; now simpl.
Qed.

Definition ex_6_6_1b: forall b1 b2: bool, bool_xor b1 b2 = bool_not (bool_eq b1 b2) :=
  fun b1 b2: bool => 
    bool_ind (fun b: bool => bool_not (bool_eq b b2) = bool_not (bool_eq b b2))
             (bool_ind (fun b: bool => bool_not (bool_eq true b) = bool_not (bool_eq true b))
                       eq_refl
                       eq_refl b2)
             (bool_ind (fun b: bool => bool_not (bool_eq false b) = bool_not (bool_eq false b))
                       eq_refl
                       eq_refl b2) b1.

Theorem ex_6_6_2a:
  forall b1 b2: bool, bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2).
Proof.
  intros b1 b2; induction b1; induction b2; now simpl.
Qed.

Definition ex_6_6_2b:
  forall b1 b2: bool, bool_not (bool_and b1 b2) = bool_or (bool_not b1) (bool_not b2) :=
  fun b1 b2 =>
    bool_ind (fun b => bool_not (bool_and b b2) = bool_or (bool_not b) (bool_not b2))
             (bool_ind (fun b => bool_not (bool_and true b) = bool_or (bool_not true) (bool_not b))
                       eq_refl
                       eq_refl b2)
             (bool_ind (fun b => bool_not (bool_and false b) = bool_or (bool_not false) (bool_not b))
                       eq_refl
                       eq_refl b2) b1.

Definition ex_6_6_3: forall b: bool, bool_not (bool_not b) = b :=
  fun b0 =>
    bool_ind (fun b => bool_not (bool_not b) = b)
             eq_refl
             eq_refl b0.

Definition ex_6_6_4: forall b, bool_or b (bool_not b) = true :=
  fun b0 =>
    bool_ind (fun b => bool_or b (bool_not b) = true)
             eq_refl
             eq_refl b0.

Theorem ex_6_6_5a: forall b1 b2, b1 = b2 -> bool_eq b1 b2 = true.
Proof.
  intros b1 b2 Heq;  rewrite Heq;
    induction b2; now simpl.
Qed.  

Print ex_6_6_5a.

Definition ex_6_6_5b: forall b1 b2, b1 = b2 -> bool_eq b1 b2 = true :=
  fun (b1 b2: bool) (Heq: b1 = b2) =>
    eq_ind_r (fun b: bool => bool_eq b b2 = true)
             (bool_ind (fun b => b1 = b -> bool_eq b b = true)
                       (fun _ : b1 = true => eq_refl)
                       (fun _ : b1 = false => eq_refl) b2 Heq) Heq.

Theorem ex_6_6_6a: forall b1 b2: bool, bool_eq b1 b2 = true -> b1 = b2.
Proof.
  unfold bool_eq; intros b1 b2;
    pattern b1; apply bool_ind; pattern b2; apply bool_ind; intro Heq;
      [idtac | elim Heq | elim Heq | idtac]; reflexivity.
Qed.

Print ex_6_6_6a.

Definition ex_6_6_6b: forall b1 b2: bool, bool_eq b1 b2 = true -> b1 = b2 :=
  fun b1 b2 : bool =>
    bool_ind
      (fun b : bool =>
         (if b then if b2 then true else false else if b2 then false else true) = true ->
         b = b2)
      (bool_ind (fun b : bool => (if b then true else false) = true -> true = b)
                (fun _ : true = true => eq_refl)
                (fun Heq : false = true => eq_ind false (fun b : bool => b = false) eq_refl true Heq)
                b2)
      (bool_ind (fun b : bool => (if b then false else true) = true -> false = b)
                (fun Heq : false = true => eq_ind false (fun b : bool => false = b) eq_refl true Heq)
                (fun _ : true = true => eq_refl) b2) b1.

Theorem ex_6_6_7: forall b1 b2: bool,
    bool_not (bool_or b1 b2) = bool_and (bool_not b1) (bool_not b2).
Proof.
  intros b1 b2; pattern b1; apply bool_ind; pattern b2; apply bool_ind;
    reflexivity.
Qed.

Theorem ex_6_6_8: forall b1 b2 b3: bool,
    bool_or (bool_and b1 b3) (bool_and b2 b3) = bool_and (bool_or b1 b2) b3.
Proof.
  intros b1 b2 b3;
    pattern b1; apply bool_ind;
      pattern b2; apply bool_ind;
        pattern b3; apply bool_ind;
          reflexivity.
Qed.

Inductive plane : Set := point : Z -> Z -> plane.

Print plane_ind.

(* Exercise 6.9 *)

Inductive vehicle : Set :=
| bicycle : nat -> vehicle
| motorized: nat -> nat -> vehicle.

Print vehicle_rec.

Definition nb_seats (v: vehicle): nat :=
  vehicle_rec (fun v: vehicle => nat)
              (fun n => n)
              (fun n n0 => n) v.

(* Exercise 6.10 *)

Inductive month : Set :=
| January | February | March     | April   | May      | June 
| July    | August   | September | October | November | December.

Definition isJanuary (m: month): bool :=
  month_rect (fun m => bool)
             true false false false
             false false false false
             false false false false m.

(* Exercise 6.11 *)

Theorem true_not_false: true <> false.
Proof.
  intros H.
  change ((fun b: bool => if b then True else False)
            false).
  rewrite <- H.
  trivial.
Qed.

(* Exercise 6.12 *)

Theorem bike_not_moto:
  forall a b c, bicycle a <> motorized b c.
Proof.
  intros a b c H.
  change ((fun v: vehicle =>
             match v with
             | bicycle _ => True
             | motorized _ _ => False
             end) (motorized b c)).
  rewrite <- H.
  trivial.
Qed.

(* Exercise 6.17 *)

Fixpoint sum_f (n: nat) (f: nat -> Z) {struct n}: Z :=
  match n with
  | O => Z0
  | S n => f n + sum_f n f
  end.

(* Exercise 6.28 *)

Inductive Z_inf_branch_tree: Set :=
| Z_inf_leaf: Z_inf_branch_tree
| Z_inf_node: Z -> (nat -> Z_inf_branch_tree) -> Z_inf_branch_tree.

Fixpoint Z_inf_branch_tree0 (depth: nat) (t: Z_inf_branch_tree): bool :=
  let search_same_level :=
      fix f (n: nat) (t: Z_inf_branch_tree): bool :=
          match t with
          | Z_inf_leaf => false
          | Z_inf_node Z0 _ => true
          | Z_inf_node _ next =>
            let next_t := next depth
            in  f depth next_t
          end
  in  match depth with
      | O => false
      | S n => if search_same_level (S n) t
              then true
              else search_same_level n t
      end.

(* Exercise 6.29 *)
Theorem plus_n_O: forall n, n = n + 0.
Proof.
  intros n;
    elim n; try reflexivity.
  clear n; intros n H; simpl;
    pattern (n + 0); rewrite <- H; reflexivity.
Qed.

(* Exercise 6.30 *)

Inductive Z_fbtree : Set :=
| Z_fleaf : Z_fbtree
| Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree.

Inductive Z_btree : Set :=
| Z_leaf : Z_btree
| Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Fixpoint f1 (t: Z_btree): Z_fbtree :=
  match t with
  | Z_leaf => Z_fleaf
  | Z_bnode v l r => Z_fnode v (fun b => if b then (f1 l) else (f1 r))
  end.

Fixpoint f2 (t : Z_fbtree): Z_btree :=
  match t with
  | Z_fleaf => Z_leaf
  | Z_fnode v f => Z_bnode v (f2 (f true)) (f2 (f false))
  end.

Lemma ex_6_30_a: forall t, f2 (f1 t) = t.
Proof.
  intros t;
    elim t; simpl; trivial.
  intros z0 zbt IH0 z1 IH1;
    rewrite IH0, IH1; reflexivity.
Qed.

Lemma ex_6_30_b: forall t, f1 (f2 t) = t.
Proof.
  intros t;
    elim t; simpl; trivial.
  intros z0 zft IH0.
  (* Equality not defined for functions *)
Abort.

(* Exercise 6.31 *)

Fixpoint mult2 (n: nat): nat :=
  match n with
  | 0 => 0
  | S n => (S (S (mult2 n)))
  end.

Theorem ex_6_31: forall n, mult2 n = n + n.
Proof.
  intros n;
    induction n; trivial.
  rewrite <- Nat.add_succ_comm; simpl;
    pattern (n + n); rewrite IHn; trivial.
Qed.

(* Exercise 6.32 *)
Fixpoint sum_n (n: nat): nat :=
  match n with
  | 0 => 0
  | S n => S n + (sum_n n)
  end.

Theorem ex_6_32: forall n, 2 * sum_n n = n * (n + 1).
Proof.
  intros n;
    induction n as [|p IHp].
  - reflexivity.
  - simpl sum_n.
    ring_simplify in IHp; ring_simplify.
    rewrite IHp; ring.
Qed.

(* Exercise 6.33 *)
Theorem ex_6_33: forall n, n <= sum_n n.
Proof.
  intros n; induction n.
  - reflexivity.
  - simpl sum_n.
    apply le_n_S.
    apply Nat.le_add_r.
Qed.

(* Exercise 6.39 *)
Fixpoint nth_option (A: Set)(n: nat)(l: list A){struct l}: option A :=
  match n, l with
  | 0, cons a tl => Some a
  | S p, cons a tl => nth_option A p tl
  | n, nil => None
  end.

Fixpoint nth_option' (A: Set)(n: nat)(l: list A){struct n}: option A :=
  match n, l with
  | 0, cons a tl => Some a
  | S p, cons a tl => nth_option A p tl
  | n, nil => None
  end.

Theorem ex_6_39: forall (A: Set) (n: nat) (l: list A), nth_option A n l = nth_option' A n l.
Proof.
  intros A n l.
  induction n, l;
    try reflexivity.
Qed.   

(* Exercise 6.40 *)
Theorem ex_6_40: forall (A: Set) (n: nat) (l: list A),
  nth_option A n l = None -> length l <= n.
Proof.
  intros A n l H.
  generalize dependent n.
  induction l; intros n H.
  - apply Nat.le_0_l.
  - destruct n;
      simpl in H; try discriminate H.
    apply le_n_S, IHl; assumption.
Qed.

(* Exercise 6.41 *)
Fixpoint ex_6_41 (A: Set) (f: A -> bool) (l: list A): option A :=
  match l with
  | nil => None
  | cons a ls => if (f a) then Some a else ex_6_41 A f ls
  end.

(* Exercise 6.42 *)
Fixpoint split' {A B: Type} (l: list (A * B)): list A * list B :=
  match l with
  | nil => (nil, nil)
  | cons (a, b) tl =>
    let (tla, tlb) := split' tl
    in  (cons a tla, cons b tlb)
  end.

Fixpoint combine {A B: Type} (l1: list A) (l2: list B): list (A * B) :=
  match l1, l2 with
  | a :: tla, b :: tlb => cons (a, b) (combine tla tlb)
  | _, _ => nil
  end.

Theorem combine_of_split {A B : Type} :
  forall l:list (A*B),
    let (l1,l2) :=  split' l
    in combine  l1 l2 = l.
Proof.
  intros l; induction l; simpl.
  - reflexivity.
  - destruct a, (split' l); simpl;
      rewrite IHl; trivial.
Qed.

(* Exercise 6.43 *)

Inductive btree (A: Set) : Set :=
| bleaf : btree A
| bnode : A -> btree A -> btree A -> btree A.        

Fixpoint c1 (t: Z_btree): btree Z :=
  match t with
  | Z_leaf => bleaf Z
  | Z_bnode v lt rt => bnode Z v (c1 lt) (c1 rt)
  end.

Fixpoint c2 (t: btree Z): Z_btree :=
  match t with
  | bleaf _ => Z_leaf
  | bnode _ v lt rt => Z_bnode v (c2 lt) (c2 rt)
  end.

Theorem ex_6_43_1:
  forall t, c1 (c2 t) = t.
Proof.
  intros t; induction t;
    try reflexivity.
  simpl; rewrite IHt1, IHt2; trivial.
Qed.

Theorem ex_6_43_2:
  forall t, c2 (c1 t) = t.
Proof.
  intros t; induction t;
    try reflexivity.
  simpl; rewrite IHt1, IHt2; trivial.
Qed.

(* Exercise 6.46 *)

Inductive htree (A: Set): nat -> Set :=
| hleaf: A -> htree A 0
| hnode: forall n: nat, A -> htree A n -> htree A n -> htree A (S n).

Theorem ex_6_46:
  forall (n: nat)(t1 t2 t3 t4: htree nat n),
    hnode nat n 0 t1 t2 = hnode nat n 0 t3 t4 -> t1 = t3.
Proof.
  intros n t1 t2 t3 t4 H.
  change (let phi :=
               fun lt =>
                 match lt in (htree _ (S n)) return (htree _ n) with
                 | hleaf _ _ => t1
                 | hnode _ _ _ tl _ => tl
                 end in phi (hnode nat n 0 t1 t2) =
                        phi (hnode nat n 0 t3 t4)).
  rewrite H; reflexivity.
Qed.

(* Exercise 6.47 *)
Definition ex_6_47:
  forall (n: nat), htree nat n :=
  fun n =>
    let rec := fix fx (l: nat): htree nat l :=
                 match l return (htree _ l) with 
                 | 0 => hleaf nat 0
                 | S m => hnode nat m m (fx m) (fx m)
                 end
    in  rec n.

(* Exercise 6.48 *)
Inductive binary_word: nat -> Set :=
| bw0 : binary_word 0
| bwc : forall n, bool -> binary_word n -> binary_word (S n).

Fixpoint binary_word_concat {n m: nat} (bw1 : binary_word n) (bw2 : binary_word m): binary_word (n + m) :=
  match bw1 in binary_word p return binary_word (p + m) with
  | bw0 => bw2
  | bwc size value next => bwc (size + m) value (binary_word_concat next bw2)
  end.

Theorem bwc_S2 :
  forall n m : nat, binary_word (n + S m) -> binary_word (S n + m).
Proof.
  intros n m H.
  assert (H0 : binary_word (n + S m) = binary_word (S n + m)).
  {
    apply f_equal;
    rewrite <- Nat.add_succ_comm;
    reflexivity.
  }

  rewrite <- H0.
  trivial.
Qed.

(* This alternative solution uses an accumulator *)

Definition bwc_S3 :
  forall n m, binary_word (n + S m) -> binary_word (S n + m) :=
  fun n m H =>
    let H0 : binary_word (n + S m) = binary_word (S n + m) :=
        f_equal binary_word
                (eq_ind (S n + m) (fun n0 => n0 = S n + m) eq_refl
                        (n + S m) (Nat.add_succ_comm n m)) in
    eq_rec (binary_word (n + S m)) (fun P : Set => P) H (binary_word (S n + m)) H0.
                        
Fixpoint binary_word_concat' {n m : nat} (bw1 : binary_word n) (bw2 : binary_word m) : binary_word (n + m) :=
  match bw1 in binary_word p return binary_word (p + m) with
  | bw0 => bw2
  | bwc sz v nx => bwc_S2 sz m (binary_word_concat' nx (bwc m v bw2))
  end.

(* 6.49 *)

Lemma discriminate_S_O {n : nat} : S n = 0 -> False.
Proof.
  intros H;
    discriminate.
Qed.

Lemma discriminate_O_S {n : nat} : 0 = S n -> False.
Proof.
  intros H;
    discriminate.
Qed.

Fixpoint binary_word_or (n:nat)(w1:binary_word n) {struct w1}:
    binary_word n -> binary_word n :=
 match w1 in binary_word p return binary_word p -> binary_word p with
   bw0 =>
     (fun w2:binary_word 0 =>
        match w2 in binary_word p' return p'=0 -> binary_word p' with
          bw0 =>
            (fun h => bw0)
        | bwc q b w2' =>
            (fun h => False_rec (binary_word (S q)) (discriminate_S_O h))
        end (refl_equal 0))
  | bwc q b1 w1' =>
      (fun w2:binary_word (S q) =>
        match w2 in binary_word p' return S q=p' -> binary_word p' with
          bw0 =>
            (fun h => False_rec (binary_word 0) (discriminate_S_O h))
        | bwc q' b2 w2' =>
            (fun h =>
               bwc q'
                  (orb b1 b2)
                  (binary_word_or q'
(* this use of eq_rec transforms w1' into an element of (binary_word (S q'))
    instead of (binary_word (S q)), thanks to the equality h. *)
                    (eq_rec (S q)
                      (fun v:nat => binary_word (pred v))
                      w1'
                      (S q')
                      (h:S q=S q'))
                      w2'))
         end (refl_equal (S q)))
  end.

Fixpoint binary_word_or (n: nat) (bw1 bw2: binary_word n): binary_word n :=
  match bw1, bw2 in binary_word p return binary_word p with
  | bw0, bw0 => bw0
  | bwc (S sz) v1 nx1,
    bwc _  v2 nx2 => bwc (S sz) (or v1 v2)
                        (binary_word_or sz nx1 nx2)
  end.

(* Exercise 6.51 *)
Theorem ex_6_51_1: forall (x y: Empty_set), x=y.
Proof.
  intros x y; elim x.
Qed.

Theorem ex_6_51_2: forall (x y: Empty_set), ~x = y.
Proof.
  intros x y H; elim x.
Qed.