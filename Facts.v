From Stdlib Require Export List.
From Stdlib Require Import Nat.
From Stdlib Require Import QArith QArith_base Qabs Qpower Qreduction Qring Qfield.
Import ListNotations.
From Stdlib Require Export Lists.List.
From Stdlib Require Import Sorting.


  (*Auxiliar notation and lemmas *)
  Notation "a '<=b' b" := (Qle_bool a b = true) (at level 70, no associativity).
  Notation "a '<=?' b" := (Qle_bool a b) (at level 70, no associativity).
  Notation "a '=b' b" := (Qeq_bool a b = true) (at level 70, no associativity).
  Notation "a '=?' b" := (Qeq_bool a b) (at level 70, no associativity).

  (* Auxiliar definition and type *)
  Definition Qltb (a b: Q): bool :=
    negb (b <=? a).

  Notation "a '<b' b" := (Qltb a b = true) (at level 70, no associativity).
  Notation "a '<?' b" := (Qltb a b) (at level 70, no associativity).


  Lemma Qltb_lt : forall a b,
      a <b b <-> a < b.
  Proof.
    intros a b; split; intros H.
    - unfold Qltb in H.
      apply negb_true_iff in H.
      apply Qnot_le_lt.
      intros H0.
      apply not_true_iff_false in H.
      destruct H.
      now apply Qle_bool_iff.
    - unfold Qltb.
      apply negb_true_iff.
      apply Qlt_not_le in H.
      apply not_true_iff_false.
      intros H0.
      destruct H.
      now apply Qle_bool_iff.
  Qed.


  Lemma Qltb_ge : forall a b,
      a <? b = false <-> b <= a.
  Proof.
    intros a b; split; intros H.
    - unfold Qltb in H.
      apply negb_false_iff in H.
      now apply Qle_bool_iff.
    - unfold Qltb.
      apply negb_false_iff.
      now apply Qle_bool_iff.
  Qed.






  Lemma nat_lt_S_non_eq_n : forall n m,
      (n < S m)%nat ->
      n <> m ->
      (n < m)%nat.
  Proof.
    intros n m H H0.
    apply PeanoNat.lt_n_Sm_le in H.
    apply PeanoNat.Nat.le_neq.
    now split.
  Qed.

      

  Lemma interval_0_1_0 : 0 <= 0 <= 1.
  Proof.
    split.
    apply Qle_refl.
    unfold Qle.
    simpl.
    apply Z.le_0_1.
  Qed.

      

Lemma interval_0_1_1 : 0 <= 1 <= 1.
Proof.
  split.
  unfold Qle.
  simpl.
  apply Z.le_0_1.
  apply Qle_refl.
Qed.

      
Lemma interval_m_1_1_0 : - (1) <=  0 <= 1.
Proof.
  apply Z.abs_le.
  apply Z.le_0_1.
Qed.

Lemma interval_m_1_1_1 : - (1) <= 1 <= 1.
Proof.
  apply Z.abs_le.
  apply Z.le_refl.
Qed.


  Lemma Qlt_0_1 : 0 < 1.
  Proof.
    unfold Qle.
    simpl.
    apply Z.lt_0_1.
  Qed.

  Lemma interval_m_1_1_fun_0 : forall x,
      - (1) <= (fun y :nat => 0) x <= 1.
  Proof.
    intros x.
    split; unfold Qle; simpl; [apply (Z.opp_nonpos_nonneg 1)|];
      apply Z.le_0_1.
  Qed.

  Lemma fun_0_eq_0 : forall x, 
      (fun x : nat => 0) x = 0.
  Proof.
    intros x; trivial.
  Qed.

Lemma plusQ_0 : 0 + 0 = 0. 
Proof.
  trivial.
Qed.


Lemma mul_0_iff : forall x y,
    x * y == 0 <-> x == 0 \/ y == 0.
Proof.
  intros x y; split; [apply Qmult_integral|]; intros [H|H]; unfold Qeq in *; simpl in *.
  rewrite Z.mul_shuffle0.
  now rewrite H.
  rewrite <- Zmult_assoc.
  rewrite H. apply Zmult_0_r.
Qed.

Lemma Qeq_plus_0_l_eq : forall x y,
    x + 0 == y <-> x == y.
Proof.
  intros x y; split; apply Qeq_trans.
  apply Qeq_sym.
  apply Qplus_0_r.
  apply Qplus_0_r.
Qed.

Lemma Qeq_plus_0_r_eq : forall x y,
    0 + x == y <-> x == y.
Proof.
  intros x y; split; apply Qeq_trans.
  apply Qeq_sym.
  apply Qplus_0_l.
  apply Qplus_0_l.
Qed.
  
Lemma Qeq_plus_compat : forall x1 x2 y1 y2,
    x1 == x2 -> y1 == y2 -> x1 + y1 == x2 + y2.
Proof.
  intros x1 x2 y1 y2 H H0.
  apply (Qeq_trans _ (x1 + y2)).
  now apply Qplus_inj_l.
  now apply Qplus_inj_r.
Qed.

Lemma Qeq_mul_compat_r : forall x y1 y2,
    y1 == y2 -> x * y1 == x * y2.
Proof.
  intros x y1 y2 H.
  case_eq (x =? 0); intros Hlf.
  - apply Qeq_bool_eq in Hlf.
    apply (Qeq_trans _ 0); [|apply Qeq_sym]; apply mul_0_iff; now left.
  - apply Qmult_inj_l; trivial.
    now apply Qeq_bool_neq in Hlf.
Qed.


Lemma Qeq_mul_compat : forall x1 x2 y1 y2,
    x1 == x2 -> y1 == y2 -> x1 * y1 == x2 * y2.
Proof.
  intros x1 x2 y1 y2 H1 H2.
  apply (Qeq_trans _ (x1 * y2)).
  now apply Qeq_mul_compat_r.
  rewrite Qmult_comm.
  rewrite (Qmult_comm x2).
  now apply Qeq_mul_compat_r.
Qed.

Lemma Qeq_mul_compat_l : forall x1 x2 y,
    x1 == x2 -> x1 * y == x2 * y.
Proof.
  intros x y1 y2 H.
  apply Qeq_mul_compat; trivial.
  apply Qeq_refl.
Qed.

  
Lemma Qleb_lt : forall a b,
    a <=? b = false <-> b < a.
Proof.
  intros a b; split; intros H.
  - apply Qnot_le_lt.
    intros H0.
    apply not_true_iff_false in H.
    destruct H.
    now apply Qle_bool_iff.
  - apply not_true_iff_false.
    intros H0.
    apply Qle_bool_iff in H0.
    apply Qle_not_lt in H0.
    now destruct H0.
Qed.

Lemma Qleb_trans : forall a b c,
    a <=b b -> b <=b c -> a <=b c.
Proof.
  intros a b c H H0.
  apply Qle_bool_iff.
  apply Qle_bool_iff in H.
  apply Qle_bool_iff in H0.
  revert H H0. apply Qle_trans.
Qed.

Lemma Qleb_plus_compat : forall a b c d,
    a <=b b -> c <=b d -> a + c <=b b + d.
Proof.
  intros a b c d H H0.
  apply Qle_bool_iff.
  now apply Qplus_le_compat; apply Qle_bool_iff.
Qed.



Lemma Qle_eq_l : forall a b c,
    a <= b -> a == c -> c <= b.
Proof.
  intros [a1 a2] [b1 b2] [c1 c2] H H0.
  unfold Qle in *.
  unfold Qeq in *.
  apply (Z.mul_le_mono_pos_r _ _ (QDen (a1 # a2))).
  apply Pos2Z.is_pos.
  rewrite Z.mul_shuffle0.
  rewrite <- H0.
  rewrite Z.mul_shuffle0.
  rewrite (Z.mul_shuffle0 (Qnum (b1 # b2))).
  apply Z.mul_le_mono_pos_r; trivial.
  apply Pos2Z.is_pos.
Qed.

Lemma Qle_eq_r : forall a b c,
    a <= b -> b == c -> a <= c.
Proof.
  intros [a1 a2] [b1 b2] [c1 c2] H H0.
  unfold Qle in *.
  unfold Qeq in *.
  apply (Z.mul_le_mono_pos_r _ _ (QDen (b1 # b2))).
  apply Pos2Z.is_pos.
  rewrite (Z.mul_shuffle0 (Qnum (c1 # c2))).
  rewrite <- H0.
  rewrite Z.mul_shuffle0.
  rewrite (Z.mul_shuffle0 (Qnum (b1 # b2))).
  apply Z.mul_le_mono_pos_r; trivial.
  apply Pos2Z.is_pos.
Qed.

Lemma Qlt_eq_l : forall a b c,
    a < b -> a == c -> c < b.
Proof.
  intros a b c H H0.
  apply Qleb_lt.
  apply Qleb_lt in H.
  apply not_true_iff_false.
  apply not_true_iff_false in H.
  intros H1; destruct H.
  apply Qle_bool_iff.
  apply Qle_bool_iff in H1.
  apply (Qle_eq_r _ _ _ H1).
  now apply Qeq_sym.
Qed.


Lemma Qlt_eq_r : forall a b c,
    a < b -> b == c -> a < c.
Proof.
  intros a b c H H0.
  apply Qleb_lt.
  apply Qleb_lt in H.
  apply not_true_iff_false.
  apply not_true_iff_false in H.
  intros H1; destruct H.
  apply Qle_bool_iff.
  apply Qle_bool_iff in H1.
  apply (Qle_eq_l _ _ _ H1).
  now apply Qeq_sym.
Qed.


  
  Lemma Qleb_plus_pos_l : forall a b c,
    a <=b b -> 0 <=b c -> a <=b c + b.
Proof.
  intros a b c H H0.
  assert (H1 := Qplus_0_l a).
  apply Qle_bool_iff.
  apply (Qle_eq_l (0 + a)); trivial.
  apply Qle_bool_iff.
  now apply Qleb_plus_compat.
Qed.

Lemma Qleb_plus_pos_r : forall a b c,
    a <=b b -> 0 <=b c -> a <=b b + c.
Proof.
  intros a b c H H0.
  assert (H1 := Qplus_0_r a).
  apply Qle_bool_iff.
  apply (Qle_eq_l (a + 0)); trivial.
  apply Qle_bool_iff.
  now apply Qleb_plus_compat.
Qed.



  Lemma Qle_plus_pos_r : forall a b c,
    a <= b -> 0 <= c -> a <= b + c.
Proof.
  intros a b c H H0.
  apply Qle_bool_iff.
  apply Qleb_plus_pos_r; now apply Qle_bool_iff.
Qed.

  Lemma Qle_plus_pos_l : forall a b c,
    a <= b -> 0 <= c -> a <= c + b.
Proof.
  intros a b c H H0.
  apply Qle_bool_iff.
  apply Qleb_plus_pos_l; now apply Qle_bool_iff.
Qed.

Lemma Qlt_plus_compat : forall a b c d,
    a < b -> c < d -> a + c < b + d.
Proof.
  intros a b c d H H0.
  apply Qplus_lt_le_compat; trivial.
  apply Qle_lteq.
  now left.
Qed.


  Lemma Qlt_plus_pos_l : forall a b c,
    a < b -> 0 <= c -> a < c + b.
Proof.
  intros a b c H H0.
  assert (H1 := Qplus_0_r a).
  apply (Qlt_eq_l (a + 0)); trivial.
  apply (Qlt_eq_r _ (b + c)). 
  now apply Qplus_lt_le_compat.
  apply Qplus_comm.
Qed.

Lemma Qlt_plus_pos_r : forall a b c,
    a < b -> 0 <= c -> a < b + c.
Proof.
  intros a b c H H0.
  assert (H1 := Qplus_0_r a).
  apply (Qlt_eq_l (a + 0)); trivial.
  now apply Qplus_lt_le_compat.
Qed.

  Lemma Qlt_plus_pos_l_2 : forall a b c,
    a <= b -> 0 < c -> a < c + b.
Proof.
  intros a b c H H0.
  assert (H1 := Qplus_0_l a).
  apply (Qlt_eq_l (0 + a)); trivial.
  now apply Qplus_lt_le_compat.
Qed.


  Lemma Qlt_plus_pos_r_2 : forall a b c,
    a <= b -> 0 < c -> a < b + c.
Proof.
  intros a b c H H0.
  assert (H1 := Qplus_0_l a).
  apply (Qlt_eq_l (0 + a)); trivial.
  apply (Qlt_eq_r _ (c + b)).
  now apply Qplus_lt_le_compat.
  apply Qplus_comm.
Qed.

Lemma Qle_plus_0_l_l : forall a b,
    a < b -> 0 + a < b.
Proof.
  intros a b H.
  assert (H1 := Qplus_0_l a).
  apply (Qlt_eq_l a); trivial.
  now apply Qeq_sym.
Qed.

Lemma Qle_plus_0_l_r : forall a b,
    a < b -> a + 0 < b.
Proof.
  intros a b H.
  assert (H1 := Qplus_0_r a).
  apply (Qlt_eq_l a); trivial.
  now apply Qeq_sym.
Qed.


Lemma Qmul_0_1_le : forall a b,
    0 < b -> 0 <= a <= 1 -> a * b <= b.
Proof.
  intros a b H H0.
  apply (Qle_eq_r _ (1 * b)); [|apply Qmult_1_l].
  apply Qmult_le_r; trivial.
  apply H0.
Qed.

Lemma Qmul_0_1_lt : forall a b c,
    b < c -> 0 <= a <= 1 -> 0 < c -> a * b < c.
Proof.
  intros a b c H H0 H1.
  case_eq (a =? 0); intros H2.
  - apply Qeq_bool_iff in H2.
    apply (Qlt_eq_l 0); trivial.
    apply Qeq_sym.
    apply mul_0_iff.
    now left.
  - apply (Qlt_le_trans _ (a * c)).
    apply (fun H => Qlt_eq_l _ _ _ H (Qmult_comm _ _)); trivial.
    apply (fun H => Qlt_eq_r _ _ _ H (Qmult_comm _ _)); trivial.
    apply Qmult_lt_compat_r; trivial.
    destruct H0 as [H0a H0b].
    apply Qle_lt_or_eq in H0a as [H0a|H0a]; trivial.
    apply Qeq_bool_neq in H2.
    destruct H2.
    now apply Qeq_sym.
    now apply Qmul_0_1_le.
Qed.

Lemma Qlt_inf_0_trans_l : forall a b c,
    a <= 0 -> b < c -> a + b < c.
Proof.
  intros a b c H H0.
  case_eq (a =? 0); intros H1.
  - apply Qeq_bool_iff in H1.
    apply (Qlt_eq_l (0 + b)); trivial.
    apply (Qlt_eq_l b); trivial.
    apply Qeq_sym.
    apply Qplus_0_l.
    apply Qplus_inj_r.
    now apply Qeq_sym.
  - apply Qle_lt_or_eq in H as [H|H].
    apply (Qlt_eq_r _ (0 + c)).
    now apply Qlt_plus_compat.
    apply Qplus_0_l.
    apply Qeq_bool_neq in H1.
    now destruct H1.
Qed.

Lemma Qle_inf_0_trans_l : forall a b c,
    a <= 0 -> b <= c -> a + b <= c.
Proof.
  intros a b c H H0.
  case_eq (a =? 0); intros H1.
  - apply Qeq_bool_iff in H1.
    apply (Qle_eq_l (0 + b)); trivial.
    apply (Qle_eq_l b); trivial.
    apply Qeq_sym.
    apply Qplus_0_l.
    apply Qplus_inj_r.
    now apply Qeq_sym.
  - apply (Qle_eq_r _ (0 + c)).
    now apply Qplus_le_compat.
    apply Qplus_0_l.
Qed.


Lemma Qlt_inf_0_trans_r : forall a b c,
    b <= 0 -> a < c -> a + b < c.
Proof.
  intros a b c H H0.
  case_eq (b =? 0); intros H1.
  - apply Qeq_bool_iff in H1.
    apply (Qlt_eq_l (a + 0)); trivial.
    apply (Qlt_eq_l a); trivial.
    apply Qeq_sym.
    apply Qplus_0_r.
    apply Qplus_inj_l.
    now apply Qeq_sym.
  - apply Qle_lt_or_eq in H as [H|H].
    apply (Qlt_eq_r _ (c + 0)).
    now apply Qlt_plus_compat.
    apply Qplus_0_r.
    apply Qeq_bool_neq in H1.
    now destruct H1.
Qed.

Lemma Qle_inf_0_trans_r : forall a b c,
    b <= 0 -> a <= c -> a + b <= c.
Proof.
  intros a b c H H0.
  case_eq (b =? 0); intros H1.
  - apply Qeq_bool_iff in H1.
    apply (Qle_eq_l (a + 0)); trivial.
    apply (Qle_eq_l a); trivial.
    apply Qeq_sym.
    apply Qplus_0_r.
    apply Qplus_inj_l.
    now apply Qeq_sym.
  - apply (Qle_eq_r _ (c + 0)).
    now apply Qplus_le_compat.
    apply Qplus_0_r.
Qed.

Lemma Qeq_bool_equiv_r : forall a b c,
    b == c -> a <=? b = (a <=? c).
Proof.
  intros a b c H.
  case_eq (a <=? c); intro H0.
  * apply Qle_bool_iff.
    apply Qle_bool_iff in H0.
    apply (Qle_eq_r _ _ _ H0).
    now apply Qeq_sym.
  * apply Qleb_lt.
    apply Qleb_lt in H0.
    apply (Qlt_eq_l _ _ _ H0).
    now apply Qeq_sym.
Qed.


Lemma Qeq_bool_equiv : forall a b c d,
    a == b -> c == d -> a <=? c = (b <=? d).
Proof.
  intros a b c d H H0.
  case_eq (b <=? d); intro H1.
  * apply Qle_bool_iff.
    apply Qle_bool_iff in H1.
    apply Qeq_sym in H.
    apply Qeq_sym in H0.
    revert H.
    apply Qle_eq_l.
    revert H1 H0.
    apply Qle_eq_r.
  * apply Qleb_lt.
    apply Qleb_lt in H1.
    apply Qeq_sym in H.
    apply Qeq_sym in H0.
    revert H0.
    apply Qlt_eq_l.
    revert H1 H.
    apply Qlt_eq_r.
Qed.

Lemma Qeq_bool_equiv_l : forall a b c,
    a == b -> a <=? c = (b <=? c).
Proof.
  intros a b c H.
  case_eq (b <=? c); intro H0.
  * apply Qle_bool_iff.
    apply Qle_bool_iff in H0.
    apply (Qle_eq_l _ _ _ H0).
    now apply Qeq_sym.
  * apply Qleb_lt.
    apply Qleb_lt in H0.
    apply (Qlt_eq_r _ _ _ H0).
    now apply Qeq_sym.
Qed.


Lemma Qeq_bool_equiv_0_r : forall a b,
    a <=? b + 0 = (a <=? b).
Proof.
  intros a b.
  apply Qeq_bool_equiv_r.
  apply Qplus_0_r.
Qed.


Lemma Qle_plus_neg_l : forall a b c,
    a <= c + b -> c < 0 -> a <= b.
Proof.
  intros a b c H H0.
  apply (fun H => Qle_eq_r _ _ _ H (Qplus_0_l _)).
  apply (Qplus_lt_l _ _ b) in H0.
  apply Qlt_le_weak.
  revert H H0.
  apply Qle_lt_trans.
Qed.

  Lemma Qle_plus_neg_r : forall a b c,
    a <= b + c -> c < 0 -> a <= b.
Proof.
  intros a b c H H0.
  apply (fun H => Qle_eq_r _ _ _ H (Qplus_0_r _)).
  apply (Qplus_lt_r _ _ b) in H0.
  apply Qlt_le_weak.
  revert H H0.
  apply Qle_lt_trans.
Qed.



Lemma Qmul_le_0_r : forall a b,
    0 <= a -> b <= 0 -> a * b <= 0.
Proof.
  intros a b H H0.
  apply (fun H => Qle_eq_l _ _ _ H (Qmult_comm _ _)).
  apply (Qle_eq_r _ (0 * a)).
  apply Qmult_le_compat_r; trivial.
  apply Qmult_0_l.
Qed.

Lemma Qmul_le_0_l : forall a b,
    a <= 0 -> 0 <= b -> a * b <= 0.
Proof.
  intros a b H H0.
  apply (Qle_eq_r _ (0 * b)).
  apply Qmult_le_compat_r; trivial.
  apply Qmult_0_l.
Qed.



Lemma map_list_app_inj : forall A B (f : A -> B) x (l : list A) (l1 l2 : list B),
    map f l = l1 ++ x :: l2 ->
    exists x' l1' l2',
      l = l1' ++ x' :: l2'
      /\ map f l1' = l1 
      /\ map f l2' = l2 
      /\ f x' = x.
Proof.
  intros A B f x l l1 l2 H.
  revert l1 H;
  induction l as [|hd tl IH]; intros l1 H.
  - now destruct (app_cons_not_nil l1 l2 x).
  - simpl in H.
    destruct l1 as [|hd1 tl1].
    * simpl.
      inversion H.
      subst.
      exists hd, [], tl.   
      repeat split.
    * inversion H.
      apply IH in H2 as [x' [l1' [l2' [H2 [H3 [H4 H5]]]]]].
      subst.
      exists x', (hd :: l1'), l2'.
      repeat split.
Qed.

Lemma one_elt_list_not_two : forall A (a1 a2 a3 : A) l1 l2,
    [a3] <> l1 ++ a1 :: a2 :: l2.
Proof.
  intros A a1 a2 a3 [|a4 [|a5 tl1]] l2;  discriminate.
Qed.



Lemma last_elt_list_eq : forall A (l1 : list A) l2 a1 a2,
    l1 ++ a1 :: nil = l2 ++ a2 :: nil -> a1 = a2.
Proof.
  intros A l1 l2 a1 a2 H.
  revert l2 H.
  induction l1 as [|hd1 tl1 IH]; intros l2 H.
  - simpl in H.
    destruct l2 as [|hd2 tl2].
    now inversion H.
    inversion H.
    now destruct (app_cons_not_nil tl2 nil a2).
  - destruct l2 as [|hd2 tl2]; inversion H.
    now destruct (app_cons_not_nil tl1 nil a1).
    now apply (IH tl2).
Qed.


  Lemma Sorted_app1 : forall (A : Type) (R : A -> A -> Prop) (l1 l2 : list A),
      Sorted R (l1 ++ l2) -> Sorted R l1.
  Proof.
    intros A R l1 l2 H.
    induction l1 as [|hd tl IH]; trivial.
    destruct tl.
    - apply Sorted_cons.
      apply Sorted_nil.
      apply HdRel_nil.
    - simpl in *.
      apply Sorted_inv in H as [H H0].
      apply Sorted_cons.
      now apply IH.
      apply HdRel_cons.
      now apply HdRel_inv in H0.
  Qed.

  Lemma Sorted_app2 : forall (A : Type) (R : A -> A -> Prop) (l1 l2 : list A),
      Sorted R (l1 ++ l2) -> Sorted R l2.
  Proof.
    intros A R l1 l2 H.
    induction l1 as [|hd tl IH]; trivial.
    apply Sorted_inv in H as [H _].
    now apply IH.
  Qed.



  Lemma length_S_fst_elt : forall A (l : list A) n,
      length l = S n ->
      exists x l', l = [x] ++ l' /\ length l' = n.
  Proof.
    intros A l n H.
    destruct l as [|hd tl].
    - inversion H.
    - exists hd, tl; split; trivial.
      now inversion H.
  Qed.


  Lemma length_S_last_elt : forall A (l : list A) n,
      length l = S n ->
      exists x l', l = l' ++ [x] /\ length l' = n.
  Proof.
    intros A l n H.
    rewrite <- length_rev in H.
    apply length_S_fst_elt in H as [x [l' [H H0]]].
    rewrite <- (rev_involutive l).
    rewrite H.
    exists x, (rev l'); split; trivial.
    now rewrite length_rev.
  Qed.

  

  Fixpoint afternlist A n (l : list A) :=
    match n with
    |O => l
    |S m => afternlist A m (tl l)
    end.

  Lemma afternlist_tl : forall A n (l: list A),
      afternlist A n (tl l) = tl (afternlist A n l).
Proof.
  intros A n.
  induction n as [|m IH]; intros l; trivial.
  simpl.
  now rewrite IH.
Qed.


  Lemma afternlist_tl_app : forall A n (l l': list A),
      (n < length l)%nat ->
      tl (afternlist A n l ++ l') = tl (afternlist A n l) ++ l'.
Proof.
  intros A n.
  induction n as [|m IH]; intros l l' Hlen; trivial.
  - destruct l as [|hd tl]; simpl; trivial.
    inversion Hlen.
  - simpl.
    rewrite IH; trivial.
    destruct l.
    now apply PeanoNat.Nat.lt_succ_l.
    now apply PeanoNat.lt_S_n.
Qed.
      
  Lemma afternlist_nil : forall A (l : list A),
      afternlist A (length l) l = [].
Proof.
  intros A l.
  induction l as [|hd tl IH]; trivial.
Qed.

  Lemma afternlist_spec : forall A (l1 l2 : list A),
      afternlist A (length l1) (l1 ++ l2) = l2.
Proof.
  intros A l1 l2.
  induction l1 as [|hd tl IH]; trivial.
Qed.

  Lemma repeat_cons_same : forall A (a : A) n,
      a :: repeat a n = repeat a n ++ [a]. 
Proof.
  intros A a n.
  induction n as [|m IH]; trivial.
  simpl.
  now rewrite IH.
Qed.
      
      

  Fixpoint repeat_seq A (l : list A) n :=
    match l with
    |[] => []
    |hd :: tl =>
       match n with
       |O => []
       |S m => repeat_seq A (tl++[hd]) m ++ [hd]
       end
    end.



  Lemma repeat_seq_one : forall A a n,
      repeat_seq A [a] n = repeat a n.
  Proof.
    intros A a n.
    induction n as [|m IH]; trivial.
    simpl.
    rewrite IH.
    symmetry.
    apply repeat_cons_same.
  Qed.

  
  Lemma repeat_seq_2_unfold : forall A (a1 a2 : A) n,
      (repeat_seq A [a1; a2] n) ++ [a2] =  
        repeat_seq A [a2; a1] (S n).
  Proof.
    intros A a1 a2 n; trivial.
  Qed.


  Lemma hd_app : forall A a1 a2 (l1 l2 : list A),
      hd a1 (l1 ++ [a2] ++ l2) = hd a1 (l1 ++ [a2]).
  Proof.
    intros A a1 a2 l1 l2.
    induction l1 as [|hd1 tl1]; trivial.
  Qed.

  Lemma hd_app_alt : forall A a1 a2 (l1 l2 : list A),
      hd a1 (l1 ++ a2 :: l2) = hd a1 (l1 ++ [a2]).
  Proof.
    intros A a1 a2 l1 l2.
    induction l1 as [|hd1 tl1]; trivial.
  Qed.

  Lemma repeat_seq_S_unfold : forall A (a a1 a2 : A) n,
      hd a (repeat_seq A [a1; a2] (S n)) :: (repeat_seq A [a1; a2] n) = repeat_seq A [a1; a2] (S n).
  Proof.
    intros A a a1 a2 n.
    revert a1 a2.
    induction n as [|n IH]; intros a1 a2; trivial.
    simpl.
    rewrite app_comm_cons.
    f_equal.
    simpl in IH.
    rewrite <- app_assoc.
    rewrite hd_app.
    apply IH.
  Qed.



  Lemma repeat_seq_S_4_unfold : forall A (a a1 a2 a3 a4 : A) n,
      hd a (repeat_seq A [a1; a2; a3; a4] (S n)) :: (repeat_seq A [a1; a2; a3; a4] n) = repeat_seq A [a1; a2; a3; a4] (S n).
  Proof.
    intros A a a1 a2 a3 a4 n.
    revert a1 a2 a3 a4.
    induction n as [|n IH]; intros a1 a2 a3 a4; trivial.
    simpl.
    rewrite app_comm_cons.
    f_equal.
    simpl in IH.
    rewrite <- app_assoc.
    rewrite hd_app.
    apply IH.
  Qed.

  Lemma repeat_seq_2 : forall A (a a1 a2 : A) n1 n2,
      hd a (repeat_seq A [a1; a2] n1 ++ repeat a2 (n2 + 2)) = hd a (repeat_seq A [a1; a2] (n1 + 2)).
  Proof.
    intros A a a1 a2 n1 n2.
    revert a1 a2.
    rewrite <- PeanoNat.Nat.add_1_r.
    rewrite PeanoNat.Nat.add_assoc.
    rewrite PeanoNat.Nat.add_1_r.
    induction n1 as [|m IH]; intros a1 a2; trivial.
    simpl (repeat_seq _ _ (S m)).
    rewrite <- app_assoc.
    rewrite hd_app.
    rewrite PeanoNat.Nat.add_assoc.
    rewrite ! PeanoNat.Nat.add_1_r.
    simpl.
    rewrite <- ! app_assoc.
    now rewrite hd_app.
  Qed.
  
  Lemma repeat_decompose : forall A (l1 l2 : list A) n1 n2,
      length l1 = n1 ->
      repeat_seq A (l1 ++ l2) (n1 + n2)%nat = repeat_seq A (l2 ++ l1) n2 ++ repeat_seq A (l1 ++ l2) n1.
  Proof.
    intros A l1 l2 n1.
    revert l1 l2. induction n1 as [|n1 IH]; intros l1 l2 n2 Hlen.
    - apply length_zero_iff_nil in Hlen.
      subst.
      destruct l2; simpl; now rewrite ! app_nil_r.
    - apply length_S_fst_elt in Hlen as [x [l3 [Hlen1 Hlen2]]].
      subst.
      simpl.
      rewrite <- app_assoc.
      rewrite (IH l3 (l2 ++ [x]) n2); trivial.
      now rewrite <- ! app_assoc.
     Qed.

 Lemma repeat_decompose2 : forall A (l : list A) q n1 n2,
      length l = n1 ->
      repeat_seq A l (n1 * q + n2)%nat = repeat_seq A l n2 ++ repeat_seq A l (n1 * q).
  Proof.
    intros A l q n1 n2 H.
    induction q as [|q IH].
    - simpl.
      rewrite PeanoNat.Nat.mul_0_r.
      destruct l; simpl; now rewrite ! app_nil_r.
    - rewrite PeanoNat.Nat.mul_succ_r.
      rewrite PeanoNat.Nat.add_comm, PeanoNat.Nat.add_assoc, PeanoNat.Nat.add_comm.
      assert (H0 := repeat_decompose _ l [] n1 (n2 + n1 * q)%nat H).
      rewrite app_nil_r in H0.
      rewrite H0.
      simpl.
      rewrite PeanoNat.Nat.add_comm.
      rewrite IH.
      rewrite <- app_assoc.
      f_equal.
      symmetry.
      rewrite PeanoNat.Nat.add_comm.
      clear H0.
      assert (H0 := repeat_decompose _ l [] n1 (n1 * q)%nat H).
      now rewrite app_nil_r in H0.
  Qed.
  
  Lemma list_app_length : forall A (l : list A) n1 n2,
      length l = (n1 + n2)%nat ->
      exists l1 l2,
        l = l1 ++ l2 /\ length l1 = n1 /\ length l2 = n2.
  Proof.
    intros A l n1 n2 H.
    revert l H; induction n1 as [|n1 IH]; intros l H.
    exists [], l; now repeat split.
    rewrite plus_Sn_m in H.
    apply length_S_fst_elt in H as [x [l' [H H0]]].
    apply IH in H0 as [l1 [l2 [H0 [H1 H2]]]].
    subst.
    exists (x :: l1), l2; now repeat split.
Qed.

Lemma f_if : forall A B (b : bool) (a1 a2 : A) (f : A -> B),
    f (if b then a1 else a2) = if b then f a1 else f a2.
Proof.
  intros A B b a1 a2 f.
  now destruct b.
Qed.

Lemma f_if2 : forall A B (b : bool) (x : A) (f1 f2 : A -> B),
   (if b then f1 else f2) x = if b then f1 x else f2 x.
Proof.
  intros A B b x f1 f2.
  now destruct b.
Qed.

Lemma if_same : forall A (b : bool) (a : A),
    (if b then a else a) = a.
Proof.
  intros A [|] a; trivial.
Qed.

Lemma nat_eqb_plus_r : forall n1 n2 n3,
    (n1 =? n2 = (n1 + n3 =? n2 + n3))%nat.
Proof.
  intros n1 n2 n3.
  case_eq (n1 + n3 =? n2 + n3)%nat; intros H.
  apply PeanoNat.Nat.eqb_eq.
  apply PeanoNat.Nat.eqb_eq in H.
  now apply PeanoNat.Nat.add_cancel_r in H.
  apply PeanoNat.Nat.eqb_neq.
  apply PeanoNat.Nat.eqb_neq in H.
  intros H0.
  destruct H.
  now subst.
Qed.



Lemma partition_list_app_inj_snd1 : forall A f (l1 l2 l l' : list A) n,
    partition f l = (l', l1 ++ n :: l2) ->
    exists l1' l2',
      l = l1' ++ n :: l2'.
Proof.
  intros A f l1 l2 l.
  revert l1.
  induction l as [|hd tl IH]; intros l1 l' n H.
  inversion H.
  now destruct (app_cons_not_nil l1 l2 n).
  simpl in H.
  rewrite (surjective_pairing (partition _ _)) in H.
  case_eq (f hd); intros H0; rewrite H0 in H.
  - rewrite (surjective_pairing (partition _ _)) in IH.
    destruct l'; inversion H.
    specialize (IH l1 l' n).
    rewrite H3, H4 in IH.
    destruct IH as [l1' [l2' IH]]; trivial.
    subst.
    exists (a :: l1'), l2'; trivial.
  - destruct l1 as [|hd1 tl1]; inversion H.
    exists nil, tl; trivial.
    rewrite (surjective_pairing (partition _ _)) in IH.
    specialize (IH tl1 l' n).
    rewrite H2, H4 in IH.
    destruct IH as [l1' [l2' IH]]; trivial.
    subst.
    exists (hd1 :: l1'), l2'; trivial.
Qed.

  

  
Lemma partition_list_app_inj_snd : forall A f (l1 l2 l3 l l' : list A) n m,
    partition f l = (l', l1 ++ n :: l2 ++ m :: l3) ->
    exists l1' l2' l3',
      l = l1' ++ n :: l2' ++ m :: l3'.
Proof.
  intros A f l1 l2 l3 l l' n m H.
  revert l1 l' H.
  induction l as [|hd tl IH]; intros l1 l' H.
  inversion H.
  now destruct (app_cons_not_nil l1 (l2 ++ m :: l3) n).
  simpl in H.
  rewrite (surjective_pairing (partition _ _)) in H.
  case_eq (f hd); intros H0; rewrite H0 in H.
  - rewrite (surjective_pairing (partition _ _)) in IH.
    destruct l'; inversion H.
    specialize (IH l1 l').
    rewrite H3, H4 in IH.
    destruct IH as [l1' [l2' [l3' IH]]]; trivial.
    subst.
    exists (a :: l1'), l2', l3'; trivial.
  - destruct l1 as [|hd1 tl1].
    inversion H.
    exists [].
    destruct (partition_list_app_inj_snd1 _ f l2 l3 tl l' m) as [l2' [l3' H5]].
    rewrite (surjective_pairing (partition _ _)).
    now rewrite H2, H4.
    subst.
    exists l2', l3'; trivial.
    rewrite (surjective_pairing (partition _ _)) in IH.
    specialize (IH tl1 l').
    inversion H.
    rewrite H2, H4 in IH.
    destruct IH as [l1' [l2' [l3' IH]]]; trivial.
    subst.
    exists (hd1 :: l1'), l2', l3'; trivial. 
Qed.



Lemma partition_snd_false : forall A f (l : list A) x,
    In x (snd (partition f l)) ->
    f x = false.
Proof.
  intros A f l x H.
  induction l as [|hd tl IH].
  inversion H.
  simpl in H.
  rewrite (surjective_pairing (partition _ _)) in H.
  case_eq (f hd); intros H0; rewrite H0 in H.
  now apply IH.
  simpl in H.
  destruct H as [H|H].
  now subst.
  now apply IH.
Qed.

Lemma partition_fst_true : forall A f (l : list A) x,
    In x (fst (partition f l)) ->
    f x = true.
Proof.
  intros A f l x H.
  induction l as [|hd tl IH].
  inversion H.
  simpl in H.
  rewrite (surjective_pairing (partition _ _)) in H.
  case_eq (f hd); intros H0; rewrite H0 in H.
  simpl in H.
  destruct H as [H|H].
  now subst.
  now apply IH.
  now apply IH.
Qed.



Lemma partition_fst_true_in : forall A (f : A -> bool) x l,
    In x l ->
    f x = true ->
    In x (fst (partition f l)).
Proof.
  intros A f x l H H0.
  induction l as [|hd tl IH].
  inversion H.
  simpl.
  rewrite (surjective_pairing (partition _ _)).
  destruct H as [H|H].
  subst.
  rewrite H0.
  now left.
  destruct (f hd);[right|]; now apply IH.
Qed.

Lemma partition_snd_false_in : forall A (f : A -> bool) x l,
    In x l ->
    f x = false ->
    In x (snd (partition f l)).
Proof.
  intros A f x l H H0.
  induction l as [|hd tl IH].
  inversion H.
  simpl.
  rewrite (surjective_pairing (partition _ _)).
  destruct H as [H|H].
  subst.
  rewrite H0.
  now left.
  destruct (f hd);[|right]; now apply IH.
Qed.

Lemma partition_fst_hd : forall A (f : A -> bool) a x l,
    In x l ->
    f x = true ->
    exists x', hd a (fst (partition f l)) = x' /\ f x' = true /\ In x' l.
Proof.
  intros A f a x l H H0.
  induction l as [|hd tl IH].
  inversion H.
  simpl.
  rewrite (surjective_pairing (partition _ _)).
  destruct H as [H|H].
  subst.
  rewrite H0.
  exists x; repeat split; trivial.
  now left.
  case_eq (f hd); intros H1.
  exists hd; repeat split; trivial.
  now left.
  apply IH in H as [x' [H2 [H3 H4]]].
  exists x'; repeat split; trivial.
  now right.
Qed.




Lemma if_true_l : forall A (b : bool) (a1 a2 : A),
    b = true ->
    (if b then a1 else a2) = a1.
Proof.
  intros A b a1 a2 H0.
  now subst.
 Qed.      

Lemma if_false_r : forall A (b : bool) (a1 a2 : A),
    b = false ->
    (if b then a1 else a2) = a2.
Proof.
  intros A b a1 a2 H0.
  now subst.
 Qed.      

Lemma if_ltb : forall (b : bool) a1 a2 a3,
    (a1 <? a3)%nat = true ->
    (a2 <? a3)%nat = true ->
    ((if b then a1 else a2) <? a3)%nat = true.
Proof.
  intros [|] a1 a2 a3 H H0; trivial.
 Qed.      


Lemma if_eqb : forall a1 a2 a3,
    ((if (a1 =? a2)%nat then a3 else a1) =? a2)%nat = (a1 =? a2)%nat && (a3 =? a2)%nat.
Proof.
  intros a1 a2 a3.
  case_eq (a1 =? a2)%nat; intros H; trivial.
 Qed.


Lemma nat_lt_sub_eq : forall a1 a2 a3,
    (0 < a2)%nat ->
    (a1 <? a2 - 1)%nat = false -> 
    ((a1 - (a2 - 1) <? a3) = (a1 <? a2 + a3 -1))%nat.
Proof.
  intros a1 a2 a3 H0 H1.
  case_eq (a1 <? a2 + a3 - 1)%nat; intros H.
  - apply PeanoNat.Nat.ltb_lt.
    apply PeanoNat.Nat.ltb_lt in H.
    apply (PeanoNat.Nat.add_lt_mono_r _ _ (a2 - 1)).
    rewrite PeanoNat.Nat.sub_add.
    rewrite PeanoNat.Nat.add_comm.
    rewrite <- PeanoNat.Nat.add_sub_swap; [trivial|now apply PeanoNat.Nat.le_succ_l].
    now apply PeanoNat.Nat.ltb_ge.
  - apply PeanoNat.Nat.ltb_ge.
    apply PeanoNat.Nat.ltb_ge in H.
     apply (PeanoNat.Nat.add_le_mono_r _ _ (a2 - 1)).
    rewrite PeanoNat.Nat.sub_add.
    rewrite PeanoNat.Nat.add_comm.
    rewrite <- PeanoNat.Nat.add_sub_swap; [trivial|now apply PeanoNat.Nat.le_succ_l].
    now apply PeanoNat.Nat.ltb_ge.
 Qed.      


Lemma nat_lt_neq : forall a1 a2,
    (a1 <? a2)%nat = true ->
    (a1 =? a2)%nat = false.
Proof.
  intros a1 a2 H0.
  apply PeanoNat.Nat.ltb_lt in H0.
  apply PeanoNat.Nat.lt_neq in H0.
  now apply PeanoNat.Nat.eqb_neq.
 Qed.



Lemma nat_lt_neq2 : forall a1 a2,
    (a2 <? a1)%nat = true ->
    (a1 =? a2)%nat = false.
Proof.
  intros a1 a2 H0.
  rewrite PeanoNat.Nat.eqb_sym.
  now apply nat_lt_neq.
Qed.



Lemma nat_lt_neq3 : forall a1 a2,
    (a1 < a2)%nat ->
    (a1 =? a2)%nat = false.
Proof.
  intros a1 a2 H0.
  apply nat_lt_neq.
  now apply PeanoNat.Nat.ltb_lt.
 Qed.



Lemma nat_lt_neq4 : forall a1 a2,
    (a2 < a1)%nat ->
    (a1 =? a2)%nat = false.
Proof.
  intros a1 a2 H0.
  apply nat_lt_neq2.
  now apply PeanoNat.Nat.ltb_lt.
Qed.


Lemma nat_lt_add_0 : forall a1 a2,
    (0 < a2)%nat ->
    (a1 <? a1 + a2 = true)%nat.
Proof.
  intros a1 a2 H0.
  apply PeanoNat.Nat.ltb_lt.
  now apply PeanoNat.Nat.lt_add_pos_r.
 Qed.      



Lemma nat_neq_lt_add_0 : forall a1 a2,
    (0 < a1)%nat ->
    (a1 + a2 =? 0 = false)%nat.
Proof.
  intros a1 a2 H0.
  rewrite PeanoNat.Nat.eqb_sym.
  apply nat_lt_neq.
  apply PeanoNat.Nat.ltb_lt.
  now apply PeanoNat.Nat.lt_lt_add_r.
 Qed.      



Lemma nat_nltb_add : forall a1 a2 a3,
    (a1 <? a2 + a3)%nat = false ->
    (a1 <? a2)%nat = false.
Proof.
  intros a1 a2 a3 H0.
  apply PeanoNat.Nat.ltb_ge in H0.
  apply PeanoNat.Nat.ltb_ge.
  revert H0.
  apply PeanoNat.Nat.le_trans.
  apply PeanoNat.Nat.le_add_r.
 Qed.


Lemma nat_ltb_add : forall a1 a2 a3,
    (a1 <? a2)%nat = true ->
    (a1 <? a2 + a3)%nat = true.
Proof.
  intros a1 a2 a3 H0.
  apply PeanoNat.Nat.ltb_lt in H0.
  apply PeanoNat.Nat.ltb_lt.
  now apply PeanoNat.Nat.lt_lt_add_r.
 Qed.



Lemma nat_nltb_trans : forall a1 a2 a3,
    (a1 <? a2)%nat = false ->
    (a2 <? a3)%nat = false ->
    (a1 <? a3)%nat = false.
Proof.
  intros a1 a2 a3 H H0.
  apply PeanoNat.Nat.ltb_ge in H.
  apply PeanoNat.Nat.ltb_ge in H0.
  apply PeanoNat.Nat.ltb_ge.
  revert H0 H.
  apply PeanoNat.Nat.le_trans.
 Qed.

Lemma nat_ltb_trans : forall a1 a2 a3,
    (a1 <? a2)%nat = true ->
    (a2 <? a3)%nat = true ->
    (a1 <? a3)%nat = true.
Proof.
  intros a1 a2 a3 H H0.
  apply PeanoNat.Nat.ltb_lt in H.
  apply PeanoNat.Nat.ltb_lt in H0.
  apply PeanoNat.Nat.ltb_lt.
  revert H H0.
  apply PeanoNat.Nat.lt_trans.
 Qed.



Lemma nat_ltb_minus_1 : forall a1 a2,
    (0 < a1)%nat ->
    (0 < a2)%nat ->
    (a1 - 1 <? a2 - 1)%nat = (a1 <? a2)%nat.
Proof.
  intros a1 a2 H1 H2.
  case_eq (a1 <? a2)%nat; intros H0.
  - apply PeanoNat.Nat.ltb_lt.
    apply PeanoNat.Nat.ltb_lt in H0.
    apply (PeanoNat.Nat.add_lt_mono_r _ _ 1%nat).
    now rewrite 2 PeanoNat.Nat.sub_add.
  - apply PeanoNat.Nat.ltb_ge in H0.
    apply PeanoNat.Nat.ltb_ge.
    now apply PeanoNat.Nat.sub_le_mono_r.
 Qed.


Lemma nat_ltb_minus_1_2 : forall a1 a2 a3,
    (0 < a2)%nat ->
    (a1 + a2 - 1 <? a2 + a3 - 1)%nat = (a1 <? a3)%nat.
Proof.
  intros a1 a2 a3 H.
  rewrite (PeanoNat.Nat.add_comm a2).
  rewrite <- 2 PeanoNat.Nat.add_sub_assoc; try solve [now apply PeanoNat.Nat.le_succ_l].
  case_eq (a1 <? a3)%nat; intros H0.
  - apply PeanoNat.Nat.ltb_lt.
    apply PeanoNat.Nat.ltb_lt in H0.
    now apply PeanoNat.Nat.add_lt_mono_r.
  - apply PeanoNat.Nat.ltb_ge in H0.
    apply PeanoNat.Nat.ltb_ge.
    now apply PeanoNat.Nat.add_le_mono_r.
Qed.




Lemma nat_lt_minus_1 : forall a,
    (0 < a)%nat ->
    (a - 1 < a)%nat.
Proof.
  intros a H0.
  apply PeanoNat.Nat.sub_lt.
  now apply PeanoNat.Nat.le_succ_l.
  apply PeanoNat.Nat.lt_0_1.
 Qed.




Lemma nat_neq_add_minus_1 : forall a1 a2,
    (0 < a1)%nat ->
    (0 < a2)%nat ->
    (a1 + a2 - 1 =? 0 = false)%nat.
Proof.
  intros a1 a2 H0 H1.
  rewrite PeanoNat.Nat.eqb_sym.
  apply PeanoNat.Nat.eqb_neq.
  apply PeanoNat.Nat.lt_neq.
  rewrite <- PeanoNat.Nat.add_sub_assoc; trivial.
  apply (PeanoNat.Nat.lt_le_trans _ a1); trivial.
  rewrite <- PeanoNat.Nat.add_0_r at 1.
  apply PeanoNat.Nat.add_le_mono_l.
  now apply PeanoNat.Nat.le_add_le_sub_r.
Qed.

Lemma nat_eq_sub_eq : forall a1 a2 a3,
    (a2 <= a1)%nat ->
    ((a1 - a2 =? a3) = (a1 =? a2 + a3))%nat.
Proof.
  intros a1 a2 a3 H1.
  case_eq (a1 =? a2 + a3)%nat; intros H.
  - apply PeanoNat.Nat.eqb_eq.
    apply PeanoNat.Nat.eqb_eq in H.
    subst.
    rewrite PeanoNat.Nat.add_comm.
    apply PeanoNat.Nat.add_sub.
  - apply PeanoNat.Nat.eqb_neq.
    apply PeanoNat.Nat.eqb_neq in H.
    intros H0; destruct H.
    subst.
    rewrite PeanoNat.Nat.add_sub_assoc, PeanoNat.Nat.add_comm; trivial.
    now rewrite PeanoNat.Nat.add_sub.
 Qed.      



Lemma nat_eq_false_le : forall a1 a2,
    (a1 <? a2)%nat = false ->
    (1 <= a2)%nat ->
    (a1 =? a2 - 1)%nat = false.
Proof.
  intros a1 a2 H H1.
  rewrite PeanoNat.Nat.eqb_sym.
  apply nat_lt_neq.
  apply PeanoNat.Nat.ltb_lt.
  apply (PeanoNat.Nat.add_lt_mono_r _ _ 1%nat).
  rewrite PeanoNat.Nat.sub_add; trivial.
  rewrite PeanoNat.Nat.add_1_r.
  apply PeanoNat.le_lt_n_Sm.
  now apply PeanoNat.Nat.ltb_ge.
Qed.


Lemma nat_eq_false_ge : forall a1 a2 a3,
    (a2 < a3)%nat ->
    (a1 <? a3)%nat = false ->
    (a1 =? a2)%nat = false.
Proof.
  intros a1 a2 a3 H H1.
  rewrite PeanoNat.Nat.eqb_sym.
  apply nat_lt_neq.
  apply PeanoNat.Nat.ltb_lt.
  apply (PeanoNat.Nat.lt_le_trans _ _ _ H).
  now apply PeanoNat.Nat.ltb_ge.
Qed.

Lemma nat_eq_add_false_lt : forall a1 a2 a3,
    (a1 < a2)%nat ->
    (a1 =? a2 + a3)%nat = false.
Proof.
  intros a1 a2 a3 H.
  apply nat_lt_neq.
  apply PeanoNat.Nat.ltb_lt.
  apply (PeanoNat.Nat.lt_le_trans _ _ _ H).
  apply PeanoNat.Nat.le_add_r.
Qed.


Lemma nat_eq_same_add_lt_0 : forall a1 a2,
    (0 < a1)%nat ->
    (a1 + a2 =? a2)%nat = false.
Proof.
  intros a1 a2 H.
  rewrite PeanoNat.Nat.eqb_sym.
  apply PeanoNat.Nat.eqb_neq.
  apply PeanoNat.Nat.lt_neq.
  now apply PeanoNat.Nat.lt_add_pos_l.
Qed.

Lemma if_if_b_same_l : forall A (b : bool) (a1 a2 a3 : A),
    (if b then (if b then a1 else a2) else a3) =
    (if b then a1 else a3).
Proof.
  intros A [|] a1 a2 a3; trivial.
Qed.


Lemma if_if_b_same_r : forall A (b : bool) (a1 a2 a3 : A),
    (if b then a1 else (if b then a2 else a3)) =
    (if b then a1 else a3).
Proof.
  intros A [|] a1 a2 a3; trivial.
Qed.

Lemma if_if_eqb_same_r : forall A b1 b2 b3 (a1 a2 : A),
    (if (b1 =? b2)%nat then a1 else (if (b1 =? b3)%nat then a1 else a2)) =
    (if (b1 =? b2)%nat || (b1 =? b3)%nat then a1 else a2).
Proof.
  intros A b1 b2 b3 a1 a2.
  case_eq (b1 =? b2)%nat; intros H; trivial.
Qed.

Definition le_plus_trans := 
fun (n m p : nat) (H : (n <= m)%nat) =>
(fun lemma : (m <= m + p)%nat =>
 trans_contra_inv_impl_morphism PreOrder_Transitive (m + p)%nat m lemma)
  (PeanoNat.Nat.le_add_r m p) H.


Lemma nat_lt_trans_minus_1 : forall a1 a2 a3 a4 a5,
    (1 <= a1)%nat ->
    (a3 < a5)%nat ->
    (a4 <? a1 + a5 + a2 - 1 = false ->
     a1 + a2 + a3 - 1 <? a4 = true)%nat.
Proof.
  intros a1 a2 a3 a4 a5 H1 H0 H.
  apply PeanoNat.Nat.ltb_lt; apply PeanoNat.Nat.ltb_ge in H; revert H; apply PeanoNat.Nat.lt_le_trans.
  rewrite <- (PeanoNat.Nat.add_assoc _ a5), (PeanoNat.Nat.add_comm a5), PeanoNat.Nat.add_assoc.
  rewrite 2 (PeanoNat.Nat.add_sub_swap (a1 + a2)); try solve [now apply le_plus_trans].
  now apply PeanoNat.Nat.add_lt_mono_l.
Qed.


Lemma nat_lt_neq_S_lt : forall a1 a2,
    (a1 <? a2 - 1 = false)%nat ->
    (a1 =? a2 - 1)%nat = false ->
    (a1 <? a2 = false)%nat .
Proof.
  intros a1 a2 H H0.
  apply PeanoNat.Nat.ltb_ge.
  apply PeanoNat.Nat.eqb_neq in H0.
  apply PeanoNat.Nat.ltb_ge in H.
  apply PeanoNat.Nat.le_sub_le_add_r in H.
  rewrite PeanoNat.Nat.add_1_r in H.
  apply PeanoNat.Nat.le_lteq in H as [H|H].
  now apply PeanoNat.lt_n_Sm_le.
  subst.
  simpl in H0.
  rewrite PeanoNat.Nat.sub_0_r in H0.
  now destruct H0.
Qed.




Lemma nat_lt_neq_S_lt2 : forall a1 a2,
    (a1 <? a2 = true)%nat ->
    (a1 =? a2 - 1)%nat = false ->
    (a1 <? a2 - 1 = true)%nat .
Proof.
  intros a1 a2 H H0.
  apply not_false_iff_true.
  apply not_false_iff_true in H.
  intros H1.
  destruct H.
  now apply nat_lt_neq_S_lt.
Qed.


Lemma nat_lt_neq_S_lt3 : forall a1 a2,
    (a1 <? a2 = false)%nat ->
    (a1 < a2 + 1)%nat ->
    (a1 = a2)%nat .
Proof.
  intros a1 a2 H H0.
  apply PeanoNat.Nat.ltb_ge in H.
  apply PeanoNat.Nat.le_lteq in H as [H|H].
  apply PeanoNat.Nat.le_succ_l in H.
  rewrite <- PeanoNat.Nat.add_1_r in H.
  apply (PeanoNat.Nat.lt_le_trans _ _ _ H0) in H.
  now apply PeanoNat.Nat.lt_irrefl in H.
  now subst.
Qed.



Lemma nat_ltb_add_same_r : forall a1 a2 a3,
    (a1 + a3 <? a2 + a3)%nat = (a1 <? a2)%nat.
Proof.
  intros a1 a2 a3.
  case_eq (a1 <? a2)%nat; intros H0.
  - apply PeanoNat.Nat.ltb_lt.
    apply PeanoNat.Nat.ltb_lt in H0.
    now apply PeanoNat.Nat.add_lt_mono_r.
  - apply PeanoNat.Nat.ltb_ge in H0.
    apply PeanoNat.Nat.ltb_ge.
    now apply PeanoNat.Nat.add_le_mono_r.
 Qed.

Lemma nat_ltb_add_same_l : forall a1 a2 a3,
    (a3 + a1 <? a3 + a2)%nat = (a1 <? a2)%nat.
Proof.
  intros a1 a2 a3.
  case_eq (a1 <? a2)%nat; intros H0.
  - apply PeanoNat.Nat.ltb_lt.
    apply PeanoNat.Nat.ltb_lt in H0.
    now apply PeanoNat.Nat.add_lt_mono_l.
  - apply PeanoNat.Nat.ltb_ge in H0.
    apply PeanoNat.Nat.ltb_ge.
    now apply PeanoNat.Nat.add_le_mono_l.
 Qed.


Lemma nat_nltb_add_r : forall a1 a2 a3,
    (a1 <? a3)%nat = false ->
    (a1 + a2 <? a3)%nat = false.
Proof.
  intros a1 a2 a3 H.
  apply PeanoNat.Nat.ltb_ge in H.
  apply PeanoNat.Nat.ltb_ge.
  now apply le_plus_trans.
 Qed.


Lemma nat_nltb_same_add_l : forall a1 a2,
    (a1 + a2 <? a2)%nat = false.
Proof.
  intros a1 a2.
  rewrite PeanoNat.Nat.add_comm.
  apply nat_nltb_add_r.
  apply PeanoNat.Nat.ltb_irrefl.
 Qed.


Lemma nat_nltb_same_add_r : forall a1 a2,
    (a1 + a2 <? a1)%nat = false.
Proof.
  intros a1 a2.
  apply nat_nltb_add_r.
  apply PeanoNat.Nat.ltb_irrefl.
 Qed.


Lemma nat_eqb_minus : forall a1 a2 a3,
    (a3 <= a1)%nat ->
    (a3 <= a2)%nat ->
    (a1 - a3 =? a2 - a3)%nat = (a1 =? a2)%nat.
Proof.
  intros a1 a2 a3 H H0.
  case_eq (a1 =? a2)%nat; intros H1.
  apply PeanoNat.Nat.eqb_eq in H1.
  subst.
  apply PeanoNat.Nat.eqb_refl.
  apply PeanoNat.Nat.eqb_neq in H1.
  apply PeanoNat.Nat.eqb_neq.
  intros H2.
  destruct H1.
  apply (PeanoNat.Nat.add_cancel_r _ _ a3) in H2.
  now rewrite 2 PeanoNat.Nat.sub_add in H2.
 Qed.




Lemma nat_minus_minus : forall a1 a2 a3,
    (a3 <= a2)%nat ->
    (a1 - (a2 - a3) = a3 + a1 - a2)%nat.
Proof.
  intros a1 a2 a3 H.
  rewrite <- (PeanoNat.Nat.add_sub a1 a3)%nat at 1.
  rewrite <- PeanoNat.Nat.sub_add_distr.
  rewrite PeanoNat.Nat.add_sub_assoc; trivial.
  rewrite (PeanoNat.Nat.add_comm a3), PeanoNat.Nat.add_sub.
  now rewrite (PeanoNat.Nat.add_comm a3).
Qed.


Lemma Qleb_mul : forall a b c,
    0 < c ->
    a * c <=? b * c = (a <=? b).
Proof.
  intros a b c Hc.
  case_eq (a <=? b); intros H.
  apply Qle_bool_iff in H.
  apply Qle_bool_iff.
  now apply Qmult_le_r.
  apply Qleb_lt.
  apply Qleb_lt in H.
  now apply Qmult_lt_r.
Qed.


Lemma Qleb_mul_alt : forall a1 a2 b1 b2 c,
    0 < c ->
    a1 == a2 ->
    b1 == b2 ->
    a1 * c <=? b1 * c = (a2 <=? b2).
Proof.
  intros a1 a2 b1 b2 c Hc Heq1 Heq2.
  rewrite <- (Qeq_bool_equiv _ _ _ _ Heq1 Heq2).
  now apply Qleb_mul.
Qed.



Lemma Qmul_more_1_le : forall q1 q2 q3,
    0 <= q1 -> 
    0 <= q2 -> 
    (1 + q1) * q2 < q3 ->
    q2 < q3.
Proof.
  intros q1 q2 q3 Hq1 Hq2 H0.
  apply Qle_lt_or_eq in Hq2 as [Hq2|Hq2].
  - apply (fun H => Qle_lt_trans _ _ _ H H0).
    apply (fun H => Qle_eq_l _ _ _ H (Qmult_1_l _ )).
    apply Qmult_le_r; trivial.
    apply Qle_plus_pos_r; trivial.
    apply Qle_refl.
  - apply (fun H => Qlt_eq_l _ _ _ H Hq2).
    apply (Qlt_eq_l _ _ 0) in H0; trivial.
    apply mul_0_iff.
    right; now apply Qeq_sym.
Qed.




Lemma n_dec_4 : forall n,
  exists q r,
    (n = 4 * q + r /\ r < 4)%nat.
Proof.
  intros n.
  rewrite (PeanoNat.Nat.div_mod n 4);[|discriminate].
  exists (n/4)%nat , (n mod 4).
  split; trivial.
  apply PeanoNat.Nat.mod_upper_bound.
  discriminate.
Qed.



Lemma if_if_inv : forall A (b1 b2 : bool) (a1 a2 a3 : A),
    (if b1 then a1 else if b2 then a2 else a3) = (if b1 || b2 then if b1 then a1 else a2 else a3).
Proof.
  intros A [|] [|] a1 a2 a3; trivial.
Qed.


Lemma lt_minus_r : forall a1 a2 a3,
    (a2 <= a1)%nat -> 
    (a1 - a2 < a3 <-> a1 < a3 + a2)%nat.
Proof.
  intros a1 a2 a3 H0.
  split; intros H.
  now apply PeanoNat.Nat.lt_sub_lt_add_r in H.
  apply (PeanoNat.Nat.add_lt_mono_r _ _ a2).
  now rewrite PeanoNat.Nat.sub_add.
Qed.


Lemma lt_minus_l : forall a1 a2 a3,
    (a2 <= a1)%nat -> 
    (a1 - a2 < a3 <-> a1 < a2 + a3)%nat.
Proof.
  intros a1 a2 a3 H0.
  split; intros H.
  now apply PeanoNat.Nat.lt_sub_lt_add_l in H.
  rewrite PeanoNat.Nat.add_comm in H.
  now apply lt_minus_r.
Qed.



Lemma le_minus_r : forall a1 a2 a3,
    (a2 <= a1)%nat -> 
    (a1 - a2 <= a3 <-> a1 <= a3 + a2)%nat.
Proof.
  intros a1 a2 a3 H0.
  split; intros H.
  now apply PeanoNat.Nat.le_sub_le_add_r in H.
  apply (PeanoNat.Nat.add_le_mono_r _ _ a2).
  now rewrite PeanoNat.Nat.sub_add.
Qed.


Lemma le_minus_l : forall a1 a2 a3,
    (a2 <= a1)%nat -> 
    (a1 - a2 <= a3 <-> a1 <= a2 + a3)%nat.
Proof.
  intros a1 a2 a3 H0.
  split; intros H.
  now apply PeanoNat.Nat.le_sub_le_add_l in H.
  rewrite PeanoNat.Nat.add_comm in H.
  now apply le_minus_r.
Qed.

Lemma eq_minus : forall a1 a2 a,
    (a <= a1)%nat -> 
    (a <= a2)%nat -> 
    (a1 - a = a2 - a -> a1 = a2)%nat.
Proof.
  intros a1 a2 a H H0 H1.
  apply (PeanoNat.Nat.add_cancel_r _ _ a) in H1.
  now rewrite 2 PeanoNat.Nat.sub_add in H1.
Qed.


Lemma nat_add_assoc_comm : forall a1 a2 a3,
    (a1 + a2 + a3 = a1 + a3 + a2)%nat.
Proof.
  intros a1 a2 a3.
  rewrite <- 2 PeanoNat.Nat.add_assoc.
  f_equal.
  apply PeanoNat.Nat.add_comm.
Qed.


Lemma lt_minus_1 : forall a,
    (0 < a)%nat -> 
    (a - 1 < a)%nat.
Proof.
  intros a H.
  apply PeanoNat.Nat.sub_lt; [trivial|apply PeanoNat.Nat.lt_0_1].  
Qed.


Lemma lt_minus_r_1 : forall a1 a2 a3,
    (1 <= a2)%nat ->
    (a2 <= a1)%nat -> 
    (a1 - (a2 - 1) < a3 <-> a1 < a3 + a2 - 1)%nat.
Proof.
  intros a1 a2 a3 H1 H0.
  split; intros H.
  apply PeanoNat.Nat.lt_sub_lt_add_r in H.
  now rewrite PeanoNat.Nat.add_sub_assoc in H.
  apply lt_minus_r.
  revert H0.
  apply PeanoNat.Nat.le_trans.
  apply PeanoNat.Nat.lt_le_incl.
  now apply lt_minus_1.
  now rewrite PeanoNat.Nat.add_sub_assoc.
Qed.


Lemma lt_minus_l_1 : forall a1 a2 a3,
    (1 <= a2)%nat ->
    (a2 <= a1)%nat -> 
    (a1 - (a2 - 1) < a3 <-> a1 < a2 + a3 - 1)%nat.
Proof.
  intros a1 a2 a3 H1 H0.
  split; intros H.
  rewrite PeanoNat.Nat.add_comm.
  now apply lt_minus_r_1 in H.
  rewrite PeanoNat.Nat.add_comm in H.
  now apply lt_minus_r_1.
Qed.

    
Lemma ltb_plus_minus_1_false_r : forall a1 a2 a3,
    (1 <= a3)%nat ->
    ((a1 <? a2 + a3 - 1) = false ->
     a3 - 1 <= a1)%nat.
Proof.
  intros a1 a2 a3 H H0.
  apply PeanoNat.Nat.ltb_ge.
  rewrite <- PeanoNat.Nat.add_sub_assoc in H0; trivial.
  revert H0.
  rewrite PeanoNat.Nat.add_comm.
  apply nat_nltb_add.
Qed.
  
  
  
Lemma ltb_false_minus_1 : forall a1 a2,
    (a1 <? a2 = false ->
    a1 <? a2 - 1 = false)%nat.
Proof.
  intros a1 a2 H.
  apply PeanoNat.Nat.ltb_ge.
  apply PeanoNat.Nat.ltb_ge in H.
  revert H.
  apply PeanoNat.Nat.le_trans.
  apply PeanoNat.Nat.le_sub_l.
Qed.
  
  
  
Lemma Qleb_plus_compat_l_l : forall a b c d,
      b == d -> a <=? b + c = (a <=? d + c).
Proof.
  intros a b c d H.
  apply Qeq_bool_equiv_r.
  now apply Qplus_inj_r.
Qed.
  
  
Lemma Qleb_plus_compat_l_r : forall a b c d,
      c == d -> a <=? b + c = (a <=? b + d).
Proof.
  intros a b c d H.
  apply Qeq_bool_equiv_r.
  now apply Qplus_inj_l.
Qed.
  
  
Lemma Qleb_plus_compat_r_l : forall a b c d,
      a == d -> a + b <=? c = (d + b <=? c).
Proof.
  intros a b c d H.
  apply Qeq_bool_equiv_l.
  now apply Qplus_inj_r.
Qed.
  
  
Lemma Qleb_plus_compat_r_r : forall a b c d,
      b == d -> a + b <=? c = (a + d <=? c).
Proof.
  intros a b c d H.
  apply Qeq_bool_equiv_l.
  now apply Qplus_inj_l.
Qed.




Lemma nat_ltq_minus_l : forall a1 a2 a3,
    (a2 <= a1)%nat ->
    (a1 - a2 <? a3)%nat = (a1 <? a2 + a3)%nat.
Proof.
  intros a1 a2 a3 H.
  case_eq (a1 <? a2 + a3)%nat; intros H0.
  apply PeanoNat.Nat.ltb_lt.
  apply lt_minus_l; trivial.
  now apply PeanoNat.Nat.ltb_lt.
  apply PeanoNat.Nat.ltb_ge.
  apply PeanoNat.Nat.le_add_le_sub_l.
  now apply PeanoNat.Nat.ltb_ge.
Qed.      




Lemma nat_ltq_minus_r : forall a1 a2 a3,
    (a2 <= a1)%nat ->
    (a1 - a2 <? a3)%nat = (a1 <? a3 + a2)%nat.
Proof.
  intros a1 a2 a3 H.
  case_eq (a1 <? a3 + a2)%nat; intros H0.
  apply PeanoNat.Nat.ltb_lt.
  apply lt_minus_r; trivial.
  now apply PeanoNat.Nat.ltb_lt.
  apply PeanoNat.Nat.ltb_ge.
  apply PeanoNat.Nat.le_add_le_sub_r.
  now apply PeanoNat.Nat.ltb_ge.
Qed.      




Lemma if_3_diff : forall x y a b,
    a <> b ->
    (if (x =? a)%nat then b else (if (x =? b)%nat then a else x)) = (if (y =? a)%nat then b else (if (y =? b)%nat then a else y)) ->
    x = y.
Proof.
    intros x y a b Hneq Heq.
    case_eq (x =? a)%nat; intros H; rewrite H in Heq.
    - apply PeanoNat.Nat.eqb_eq in H; subst x.
      case_eq (y =? a)%nat; intros H0; rewrite H0 in Heq.
      * apply PeanoNat.Nat.eqb_eq in H0; now subst y.
      * case_eq (y =? b)%nat; intros H1; rewrite H1 in Heq.
        -- rewrite Heq in Hneq.
           now destruct Hneq.
        -- now rewrite Heq, PeanoNat.Nat.eqb_refl in H1.
    - case_eq (x =? b)%nat; intros H0; rewrite H0 in Heq.
      * apply PeanoNat.Nat.eqb_eq in H0; subst x.
        case_eq (y =? a)%nat; intros H1; rewrite H1 in Heq.
        -- rewrite Heq in Hneq.
           now destruct Hneq.
        -- case_eq (y =? b)%nat; intros H2; rewrite H2 in Heq.
           ** apply PeanoNat.Nat.eqb_eq in H2.
              now subst.
           ** now rewrite Heq, PeanoNat.Nat.eqb_refl in H1.
      * case_eq (y =? a)%nat; intros H1; rewrite H1 in Heq.
        -- now rewrite Heq, PeanoNat.Nat.eqb_refl in H0.
        -- case_eq (y =? b)%nat; intros H2; rewrite H2 in Heq; trivial.
           now rewrite Heq, PeanoNat.Nat.eqb_refl in H.
Qed.



Lemma if_equal : forall A (b1 b2 : bool) (a1 a2 a3 a4 : A),
    b1 = b2 ->
    a1 = a2 ->
    a3 = a4 ->
    (if b1 then a1 else a3) = (if b2 then a2 else a4).
Proof.
  intros A b1 b2 a1 a2 a3 a4 H H0 H1.
  now subst.
Qed.


Lemma if_equal_Q : forall (b1 b2 : bool) a1 a2 a3 a4,
    b1 = b2 ->
    a1 == a2 ->
    a3 == a4 ->
    (if b1 then a1 else a3) == (if b2 then a2 else a4).
Proof.
  intros b1 b2 a1 a2 a3 a4 H H0 H1.
  subst.
  now destruct b2.
Qed.



Lemma equivpermut_wf_compo6 : forall (rho1 rho2 : nat -> nat) P a (b : nat -> bool) c,
    (forall x y : nat,
          P x /\ b x = true -> P y /\ b y = true ->
          a <= x < c -> a <= y < c ->
        rho1 x = rho1 y -> x = y)%nat ->
    (forall x y : nat,
         P x /\ b x = false -> P y /\ b y = false ->
         a <= x < c -> a <= y < c ->
        rho2 x = rho2 y -> x = y)%nat ->
    (forall x y : nat,
        P x -> P y ->
        b x = true -> b y = false -> a <= x < c -> a <= y < c ->
        rho1 x <> rho2 y)%nat ->
    (forall x y : nat,
        P x -> P y ->
        a <= x < c ->
        a <= y < c ->
        (if b x then rho1 x else rho2 x) = (if b y then rho1 y else rho2 y) ->
        x = y)%nat.
Proof.
  intros rho1 rho2 P a b c Hwf1 Hwf2 Hwf3 x y Hpx Hpy Hx Hy Hrho.
  case_eq (b x); intros H; case_eq (b y); intros H0; rewrite H, H0 in Hrho.
  apply Hwf1; trivial; now split.
  now destruct (Hwf3 _ _ Hpx Hpy H H0 Hx Hy).
  destruct (Hwf3 _ _ Hpy Hpx H0 H Hy Hx).
  now symmetry.
  apply Hwf2; trivial; now split.
Qed.



  
  Lemma app_cons2_in : forall A (n m : A) l1 l2 l3 l4 l5,
    l1 ++ l2 = l3 ++ n :: l4 ++ m :: l5 ->
    (exists l, l1 = l3 ++ n :: l4 ++ m :: l \/ l2 = l ++ n :: l4 ++ m :: l5) \/ (exists la lb, l1 = l3 ++ n :: la /\ l2 = lb ++ m :: l5).
Proof.
  intros A n m l1 l2.
  revert n m.
  induction l1 as [|hd tl]; intros n m l3 l4 l5 H.
  - left.
    exists l3; now right.
  - destruct l3 as [|hd3 tl3].
    * inversion H.
      destruct l4 as [|hd4 tl4].
      -- simpl.
         destruct l5 as [|hd5 tl5].
         ** apply app_eq_unit in H2 as [[H2 H3]|[H2 H3]]; subst.
            right; exists [], []; now split.
            left; exists []; now left.
         ** apply (IHtl m hd5 [] [] tl5) in H2 as [[l [H2|H2]]|[la [lb [H2 H3]]]]; subst; simpl.
            left; exists (hd5 :: l); now left.
            right; exists tl, l; now split.
            left; exists la; now left.
      -- apply (IHtl hd4 m [] tl4 l5) in H2 as [[l [H2|H2]]|[la [lb [H2 H3]]]]; subst; simpl.
         left; exists l; now left.
         right; exists tl, (l ++ hd4 :: tl4); split; trivial.
         now rewrite <- app_assoc, app_comm_cons.
         right; exists (hd4 :: la), lb; split; trivial.    
    * inversion H.
      subst.
      apply (IHtl n m tl3 l4 l5) in H2 as [[l [H2|H2]]|[la [lb [H2 H3]]]]; subst; simpl.
      left; exists l; now left.
      left; exists l; now right.
      right; exists la, lb; now split.
  Qed.





Lemma partition_snd_filter : forall A (f : A -> bool) l,
    snd (partition f l) = filter (fun x => negb (f x)) l.
Proof.
  intros A f l.
  induction l as [|hd tl IH]; trivial.
  simpl.
  rewrite (surjective_pairing (partition _ _)).
  case_eq (f hd); intros H; trivial.
  simpl.
  now f_equal.
Qed.



Lemma filter_length : forall A (f : A -> bool) l,
    (length l = length (filter f l) + length (filter (fun x => negb (f x)) l))%nat.
Proof.
  intros A f l.
  induction l as [|hd tl IH]; trivial.
  simpl.
  rewrite IH.
  case_eq (f hd); intros H; trivial.
Qed.




Lemma partition_snd_false_in2: forall (A : Type) (f : A -> bool) (l : list A) (x : A),
    In x (snd (partition f l)) -> f x = false /\ In x l.
Proof.
  intros A f l x H.
  split.
  revert H.
  apply partition_snd_false.
  induction l as [|hd tl IH].
  inversion H.
  simpl in H.
  rewrite (surjective_pairing (partition _ _)) in H.
  destruct (f hd).
  apply IH in H.
  now right.
  destruct H as [H|H].
  subst; now left.
  apply IH in H.
  now right.
Qed.


Definition le_plus_minus := 
fun (n m : nat) (H : (n <= m)%nat) =>
eq_sym
  (eq_ind_r (fun n0 : nat => n0 = m) (PeanoNat.Nat.sub_add n m H)
     (PeanoNat.Nat.add_comm n (m - n))).

Lemma Nat_add_sub2 : forall m n : nat, (m + n - m)%nat = n.
Proof.
  intros. now rewrite PeanoNat.Nat.add_comm, PeanoNat.Nat.add_sub.
Qed.
