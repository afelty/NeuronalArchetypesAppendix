From Stdlib Require Import List SetoidList.
From Stdlib Require Import Arith.
From Stdlib Require Import Nat.
Import ListNotations.
From Stdlib Require Import Sorting.
Require Import Facts.


Fixpoint sort_list_aux A (l : list A) (f : A -> nat) x :=
  match l with
  |[] => [x]
  |hd :: tl => if (f hd <? f x)%nat
               then hd :: sort_list_aux A tl f x
               else x :: l 
  end.

Fixpoint sort_list A l f :=
  match l with
  |[] => []
  |hd :: tl => @sort_list_aux A (sort_list A tl f) f hd
  end.


Lemma sort_list_aux_in : forall A (f : A -> nat) ln x y,
    In y (x :: ln) <-> In y (sort_list_aux A ln f x).
Proof.
  intros A f ln x y.
  induction ln as [|hd tl IH]; split; intros H; try solve [destruct H as [H|H]; [now left|inversion H]].
  - destruct H as [H|[H|H]].
    * subst.
      simpl.
      destruct (f hd <? f y)%nat.
      right.
      apply IH.
      now left.
      now left.
    * subst. simpl.
      destruct (f y <? f x)%nat.
      now left.
      right; now left.
    * simpl.
      destruct (f hd <? f x)%nat.
      right.
      apply IH.
      now right.
      right; now right.
  - simpl in H.
    destruct (f hd <? f x)%nat.
    * destruct H as [H|H].
      -- subst.
         right; now left.
      -- apply IH in H.
         destruct H as [H|H].
         subst; now left.
         right; now right.
    * destruct H as [H|[H|H]].
      -- subst.
         now left.
      -- subst.
         right; now left.
      -- right; now right.
Qed.

Lemma sort_list_aux_length : forall A (f : A -> nat) ln x,
    length (x :: ln) = length (sort_list_aux A ln f x).
Proof.
   intros A f ln x.
  induction ln as [|hd tl IH]; trivial.
  simpl.
  destruct (f hd <? f x)%nat; simpl; trivial.
  now rewrite <- IH.
Qed.


Lemma sort_list_in : forall A (f : A -> nat) ln x,
    In x ln <-> In x (sort_list A ln f).
Proof.
   intros A f ln x; induction ln as [|hd tl IH]; split; intros H; trivial.
  - simpl. apply sort_list_aux_in.
    simpl.
    destruct H as [H|H].
    now left.
    right. now apply IH.
  - simpl in H. apply sort_list_aux_in in H.
    simpl in H.
    destruct H as [H|H].
    now left.
    right. now apply IH.
Qed.

Lemma sort_list_length : forall A (f : A -> nat) ln,
    length ln = length (sort_list A ln f).
Proof.
   intros A f ln; induction ln as [|hd tl IH]; trivial.
  simpl. rewrite <- sort_list_aux_length.
  simpl. now f_equal.
Qed.


Lemma sort_list_app_inj_aux : forall A (f : A -> nat) ln x y l1 l2,
    sort_list_aux A ln f x = l1 ++ y :: l2 ->
    exists l1' l2',
      x = y \/
        ln = l1' ++ y :: l2'.
Proof.
   intros A f ln x y l1 l2 H.
  revert l1 H;
    induction ln as [|hd tl IH]; intros l1 H.
  - simpl in H.
    destruct l1 as [|hd1 tl1].
    * inversion H.
      subst.
      exists [], [].
      now left.
    * inversion H.
      now destruct (app_cons_not_nil tl1 l2 y).
  - simpl in H.
    destruct (f hd <? f x)%nat.
    * destruct l1 as [|hd1 tl1]; inversion H; subst.
      -- exists [], tl.
         now right.
      -- apply IH in H2 as [l1'[l2'[H2|H2]]]; subst.
         exists [], [].
         now left.
         exists (hd1 :: l1'), l2'.
         rewrite app_comm_cons.
         now right.
    * destruct l1 as [|hd1 tl1]; inversion H; subst.
      -- exists [], [].
         now left.
      -- exists tl1, l2.
         now right.
Qed.


Lemma sort_list_app_inj_aux2 : forall A (f : A -> nat) ln x y1 y2 l1 l2 l3,
    sort_list_aux A ln f x = l1 ++ y1 :: l2 ++ y2 :: l3 ->
    exists l1' l2' l3',
      x = y1 /\ ln = l2' ++ y2 :: l3' \/
        x = y2 /\ ln = l1' ++ y1 :: l2' \/
        ln = l1' ++ y1 :: l2' ++ y2 :: l3' \/
        ln = l1' ++ y2 :: l2' ++ y1 :: l3'.
Proof.
   intros A f ln x y1 y2 l1 l2 l3 H.
  revert l1 H;
    induction ln as [|hd tl IH]; intros l1 H.
  - simpl in H.
    destruct l1 as [|hd1 tl1].
    * inversion H.
      now destruct (app_cons_not_nil l2 l3 y2).
    * inversion H.
      now destruct (app_cons_not_nil tl1 (l2 ++ y2 :: l3) y1).
  - simpl in H.
    destruct (f hd <? f x)%nat.
    * destruct l1 as [|hd1 tl1]; inversion H; subst.
      -- apply sort_list_app_inj_aux in H2 as [l2' [l3' [H2|H2]]]; subst.
         exists [], tl, []; right; now left.
         exists [], l2', l3'.
         do 2 right. now left.
      -- apply IH in H2 as [l1'[l2'[l3'[[H2 H3]|[[H2 H3]|[H2|H2]]]]]]; subst.
         exists [], (hd1 :: l2'), l3'; now left.
         exists (hd1 :: l1'), l2', []; right; now left.
         exists (hd1 :: l1'), l2', l3'; do 2 right; now left.
         exists (hd1 :: l1'), l2', l3'; now do 3 right.
    * destruct l1 as [|hd1 tl1]; inversion H; subst.
      -- exists [], l2, l3.
         now left.
      -- exists tl1, l2, l3.
         do 2 right; now left.
Qed.



Lemma sort_list_app_inj : forall A (f : A -> nat) ln x l1 l2,
    sort_list A ln f = l1 ++ x :: l2 ->
    exists l1' l2',
      ln = l1' ++ x :: l2'.
Proof.
   intros A f ln x l1 l2 H.
  revert l1 l2 H;
    induction ln as [|hd tl IH]; intros l1 l2 H.
  - now destruct (app_cons_not_nil l1 l2 x).
  - simpl in H.
    apply sort_list_app_inj_aux in H as [l1'[l2'[H|H]]].
    * subst.
      exists [], tl; trivial.
    * apply IH in H as [l1'' [l2'' H]].
      subst.
      exists (hd :: l1''), l2''.
      now rewrite app_comm_cons.
Qed.


Lemma sort_list_app_inj2 : forall A (f : A -> nat) ln x y l1 l2 l3,
    sort_list A ln f = l1 ++ x :: l2 ++ y :: l3 ->
    exists l1' l2' l3',
      ln = l1' ++ x :: l2' ++ y :: l3' \/
        ln = l1' ++ y :: l2' ++ x :: l3'.
Proof.
   intros A f ln x y l1 l2 l3 H.
  revert x y l1 l2 l3 H;
    induction ln as [|hd tl IH]; intros x y l1 l2 l3 H.
  - now destruct (app_cons_not_nil l1 (l2 ++ y :: l3) x).
  - simpl in H.
    apply sort_list_app_inj_aux2 in H as [l1'[l2'[l3'[[H H0]|[[H H0]|[H|H]]]]]].
    * apply sort_list_app_inj in H0 as [l4' [l5' H0]].
      subst.
      exists [], l4', l5'; now left.
    * apply sort_list_app_inj in H0 as [l4' [l5' H0]].
      subst.
      exists [], l4', l5'; now right.
    * apply IH in H as [l1'' [l2'' [l3'' [H|H]]]]; subst; rewrite app_comm_cons; exists (hd :: l1''), l2'', l3''.
      now left.
      now right.
    * apply IH in H as [l1'' [l2'' [l3'' [H|H]]]]; subst; rewrite app_comm_cons; exists (hd :: l1''), l2'', l3''.
      now right.
      now left.
Qed.

Lemma sort_list_aux_sorted : forall A (f : A -> nat) a l,
    (forall n, In n l ->
               f a <> f n) ->
    Sorted  (fun x y => (f x < f y)%nat) l ->
    Sorted (fun x y => (f x < f y)%nat)
           (sort_list_aux A l f a).
Proof.
  intros A f a l H H0.
  induction l as [|hd tl IH].
  - simpl.
    apply Sorted_cons.
    apply Sorted_nil.
    apply HdRel_nil.
  - simpl.
    case_eq (f hd <? f a)%nat; intros H1.
    * apply Sorted_cons.
      -- apply IH.
         intros n H2.
         apply H.
         now right.
         now apply Sorted_inv in H0 as [H0 _].
      -- apply SetoidList.In_InfA.
         intros y H3.
         apply sort_list_aux_in in H3 as [H3|H3].
         subst.
         now apply Nat.ltb_lt in H1.
         apply Sorted_extends in H0.
         now apply (proj1 (Forall_forall _ _)) with y in H0.
         intros n1 n2 n3; apply Nat.lt_trans.
    * apply Sorted_cons; trivial.
      apply HdRel_cons.
      apply Nat.ltb_ge in H1.
      apply Nat.le_neq.
      split; trivial.
      apply H.
      now left.
Qed.








Lemma sorted_sup_length_fst_app : forall A (f : A -> nat) x l1 l2,
    Sorted (fun x y => (f x < f y)%nat) (l1 ++ l2) ->
    In x l2 ->
    (length l1 <= f x)%nat.
Proof.
  intros A f x l1 l2 H Hin.
  assert (Hn := Nat.eq_refl (length l1)).
  revert Hn.
  set (n:= length l1) at 2.
  clearbody n.
  revert l1 x l2 H Hin.
  induction n as [|m IH]; intros l1 x l2 H Hin Hn.
  - apply length_zero_iff_nil in Hn.
    subst.
    apply Nat.le_0_l.
  - apply length_S_last_elt in Hn as [y [l3 [H0 H1]]].
    subst l1.
    apply Sorted_app1 in H as H2.
    apply (IH _ _ _ H2 (in_eq _ _)) in H1.
    rewrite <- app_assoc in H.
    apply Sorted_app2 in H.
    apply Sorted_extends in H as H4; [|intros x' y' z; apply Nat.lt_trans].
    apply (proj1 (Forall_forall _ _)) with x in H4; trivial.
    apply le_n_S in H1.
    apply Nat.le_succ_l in H4.
    rewrite length_app, Nat.add_1_r.
    revert H1 H4.
    apply (Nat.le_trans _ _ _).
Qed.

Lemma sorted_inf_length_fst_app : forall A (f : A -> nat) x l1 l2,
    Sorted (fun x y => (f x < f y)%nat) (l1 ++ l2) ->
    (forall x, In x (l1 ++ l2) -> (f x < length (l1 ++ l2))%nat) ->
    In x l1 ->
    (f x < length l1)%nat.
Proof.
  intros A f x l1 l2 H Hleng.
  assert (Hn := Nat.eq_refl (length l2)).
  revert Hn.
  set (n:= length l2) at 2.
  clearbody n.
  revert l1 x l2 H Hleng.
  induction n as [|m IH]; intros l1 x l2 H Hleng Hn Hin.
  - apply length_zero_iff_nil in Hn.
    subst.
    rewrite app_nil_r in Hleng.
    now apply Hleng.
  - apply length_S_fst_elt in Hn as [y [l3 [H0 H1]]].
    subst l2.
    rewrite app_assoc in H.
    rewrite app_assoc in Hleng.
    assert (In y (l1 ++ [y])) as H0.
    apply in_or_app.
    right; now left.
    apply (IH (l1 ++ [y]) y l3 H Hleng H1) in H0.
    rewrite length_app in H0.
    rewrite Nat.add_1_r in H0.
    apply in_split in Hin as [l4 [l5 Hin]].
    subst.
    rewrite <- ! app_assoc in H.
    apply Sorted_app2 in H.
    rewrite <- app_comm_cons in H.
    apply Sorted_extends in H as H4; [|intros x' y' z; apply Nat.lt_trans].
    apply (proj1 (Forall_forall _ _)) with y in H4; trivial.
    apply Nat.le_succ_l in H4.
    apply (Nat.le_lt_trans _ _ _ H4) in H0.
    now apply PeanoNat.lt_S_n in H0.
    apply in_or_app.
    right; now left.
Qed.

Lemma sorted_eq_length_fst_eq : forall A (f : A -> nat) x l1 l2,
    Sorted (fun x y => (f x < f y)%nat) (l1 ++ x :: l2) ->
    (forall x0,
        In x0 (l1 ++ x :: l2) ->
        (f x0 < length (l1 ++ x :: l2))%nat) ->
    (length l1 = f x)%nat.
Proof.
  intros A f x l1 l2 H Hin.
  apply Nat.le_antisymm.
  apply (sorted_sup_length_fst_app _ _ _ _ _ H).
  now left.
  assert (H0 := sorted_inf_length_fst_app _ f x (l1 ++ [x]) l2).
  rewrite (length_app l1 [x]) in H0.
  rewrite Nat.add_1_r in H0.
  apply PeanoNat.lt_n_Sm_le.
  apply H0.
  now rewrite <- app_assoc.
  intros x0 H1.
  rewrite <- app_assoc.
  apply Hin.
  now rewrite <- app_assoc in H1.
  apply in_or_app.
  right; now left.
Qed.


