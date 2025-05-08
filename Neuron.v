Require Export List.
Require Export Setoid.
Require Export SetoidPermutation.
Require Export Relation_Definitions.
Require Import Arith.
Require Import ZArith.
Require Export BinNums.
Require Import BinPos BinNat Nat.
Require Import Logic.
Require Import QArith QArith_base Qabs Qpower Qreduction Qring Qfield.
Import ListNotations.
Require Export Lists.List.
Require Import Sorting.
Require Import Facts.

(*Definition of the features of a neuron *)
Record NeuronFeature :=
  MakeFeat {
      Id : nat; (* identifier *)
      Weights: nat -> Q; 
      Leak_Factor: Q;
      Tau: Q;
      LeakRange: 0 <= Leak_Factor <= 1;
      PosTau: 0 < Tau;
      WRange: forall x, (-1%Q) <= Weights x <= 1;
      WId : Weights Id = 0;
    }.

(* Definition of a neuron *)
Record Neuron :=
  MakeNeuron {
      Output: list bool; (*memory of the outputs of the neuron since time 0 *)
      CurPot: Q;
      Feature : NeuronFeature;
      CurPot_Output : (Tau Feature <=? CurPot) = hd false Output;
    }.



(* Trivial Neuron *)
Lemma setneuron_curpot_output : forall nf, (Tau nf <=? 0) = hd false [false].
Proof.
  intros; apply Qleb_lt; apply nf.
Qed.

Definition SetNeuron (nf : NeuronFeature): Neuron:=
  MakeNeuron [false] 0 nf (setneuron_curpot_output _).


Lemma feature_set_neuron : forall nf, 
    Feature (SetNeuron nf) = nf.
Proof.
  intros; trivial.
Qed.


Definition NeuronEmpty := SetNeuron (MakeFeat 0 (fun _ => 0) 0 1 interval_0_1_0 Qlt_0_1 (fun _ => interval_m_1_1_0) (fun_0_eq_0 0)).


(** Well-formedness of a neuron **)
Definition well_formed_neuron n :=
  (exists l, Output n = l ++ [false]).

(** Potential **)

(* Compute the potential coming from the inputs (0 to len) *)

Fixpoint potential (Weights : nat -> Q) (inp : nat -> bool) (len : nat) : Q :=
  match len with
  | O => 0
  | S m => if inp m
           then (potential Weights inp m) + Weights m
           else (potential Weights inp m)
  end.

(* Compute the potential of the neuron (added potential + remaining potential) *)

Definition NextPotential (n : Neuron) (inp : nat -> bool) (len : nat) : Q :=
  if Tau (Feature n) <=? CurPot n
  then (potential (Weights (Feature n)) inp len)
  else (potential (Weights (Feature n)) inp len) + (Leak_Factor (Feature n)) * (CurPot n).


(* Give us if the neuron fires or not *)
Definition NextOutput n p := Tau (Feature n) <=? p.

(* Compute the next state of a neuron for a particular input *)
Definition NextNeuron (inp : nat -> bool) (len : nat) (n : Neuron) :=
  let next_potential := NextPotential n inp len in
  MakeNeuron (NextOutput n next_potential :: Output n) next_potential (Feature n) (eq_refl _).



(* Compute the state of a given neuron after n unit of time for a particular series of inputs *)

Fixpoint AfterNstepsNeuron (n: Neuron) (inp: list (nat -> bool)) len : Neuron :=
  match inp with
  | nil => n
  | h::tl => NextNeuron h len (AfterNstepsNeuron n tl len) 
  end.



(* Lemmas on features *)

Lemma next_neuro_same_feature : forall inp n len,
    Feature (NextNeuron inp len n) = Feature n.
Proof.
  intros inp n len; trivial.  
Qed.


Lemma after_nsteps_same_feature : forall inp n len, 
    Feature (AfterNstepsNeuron n inp len) =
      Feature n.
Proof.
  induction inp as [|i inp IH]; intros n len; simpl; trivial.
Qed.



(* Lemma : CurPot for NextNeuron*)

Lemma curpot_next_neuron_unfold : forall i n len,
    CurPot (NextNeuron i len n) =
      (if Tau (Feature n) <=? CurPot n
       then potential (Weights (Feature n)) i len
       else
         potential (Weights (Feature n)) i len +
           Leak_Factor (Feature n) * CurPot n).
Proof.
  intros i n len. trivial.
Qed.

(* unfold NextOutput and NextPotential*)

Lemma nextoutput_nextpotential : forall n inp len,
    NextOutput n (NextPotential n inp len) =
      (Tau (Feature n) <=?
         potential (Weights (Feature n)) inp len +
           (if Tau (Feature n) <=? CurPot n
            then 0
            else Leak_Factor (Feature n) * CurPot n)).
Proof.
  intros n inp len.
  unfold NextOutput, NextPotential.
  destruct (Tau (Feature n) <=? CurPot n); trivial.
  symmetry.
  apply Qeq_bool_equiv_0_r.
Qed.


(* Well-formedness *)


Lemma well_formed_setneuron : forall nf,
    well_formed_neuron (SetNeuron nf).
Proof.
  intros nf.
  exists []; trivial.
Qed.


Lemma well_formed_nextneuron : forall i n len,
    well_formed_neuron n ->
    well_formed_neuron (NextNeuron i len n).
Proof.
  intros i n len [l H].
  unfold well_formed_neuron.
  simpl.
  rewrite H.
  now exists (NextOutput n (NextPotential n i len) :: l).
Qed.


Lemma well_formed_afterN : forall inp n len,
    well_formed_neuron n ->
    well_formed_neuron (AfterNstepsNeuron n inp len).
Proof.
  intros inp n len H.
  induction inp as [|i inp IH]; trivial.
  simpl.
  now apply well_formed_nextneuron.
Qed.



(*** Equivalence ***)

Definition EquivFeature (nf1 nf2: NeuronFeature) len : Prop :=
  Id nf1 = Id nf2 /\
    (forall id, (id < len)%nat -> Weights nf1 id == Weights nf2 id) /\
    Leak_Factor nf1 == Leak_Factor nf2 /\
    Tau nf1 == Tau nf2.

Definition EquivNeuron (n1 n2: Neuron) len : Prop :=
  EquivFeature (Feature n1) (Feature n2) len /\
    Output n1 = Output n2 /\
    CurPot n1 == CurPot n2.


(** Reflexivity **)

Lemma EquivNeuron_refl : forall n len,              
    EquivNeuron n n len.
Proof.
  intros n len.
  repeat split; trivial.
Qed.


(** Symmetry **)

Lemma EquivNeuron_sym : forall n1 n2 len,              
    EquivNeuron n1 n2 len ->
    EquivNeuron n2 n1 len.
Proof.
  intros n1 n2 len [[Hid [Hw [Hlk Htau]]] [Hout Hcur]].
  repeat split; try solve [now symmetry].
  intros id H.
  apply Qeq_sym.
  now apply Hw.
Qed.


(** Transitivity **)

Lemma EquivNeuron_trans : forall n1 n2 n3 len,              
    EquivNeuron n1 n2 len ->
    EquivNeuron n2 n3 len ->
    EquivNeuron n1 n3 len.
Proof.
  intros n1 n2 n3 len [[Hid1 [Hw1 [Hlk1 Htau1]]] [Hout1 Hcur1]] [[Hid2 [Hw2 [Hlk2 Htau2]]] [Hout2 Hcur2]].
  repeat split.
  - now rewrite Hid1.
  - intros id Hid.
    specialize (Hw1 _ Hid).
    specialize (Hw2 _ Hid).
    revert Hw1 Hw2.
    apply Qeq_trans.
  - revert Hlk1 Hlk2.
    apply Qeq_trans.
  - revert Htau1 Htau2.
    apply Qeq_trans.
  - now rewrite Hout1.
  - revert Hcur1 Hcur2.
    apply Qeq_trans.
Qed.



Lemma potential_equiv_weight : forall w1 w2 inp len,
    (forall id : nat,
        (id < len)%nat -> w1 id == w2 id) ->
    potential w1 inp len ==
      potential w2 inp len.
Proof.
  intros w1 w2 inp len H.
  induction len as [|m IH]; [apply Qeq_refl|].
  simpl.
  destruct (inp m).
  apply Qeq_plus_compat.
  apply IH; intros id H1; apply H; now apply Nat.lt_lt_succ_r.
  apply H.
  apply Nat.lt_succ_diag_r.
  apply IH; intros id H1; apply H; now apply Nat.lt_lt_succ_r.
Qed.


Lemma potential_equiv_inp : forall w inp1 inp2 len,
    (forall m, (m < len)%nat -> inp1 m = inp2 m) ->
    potential w inp1 len ==
      potential w inp2 len.
Proof.
  intros w inp1 inp2 len H.
  induction len as [|m IH]; [apply Qeq_refl|].
  simpl.
  rewrite H; [|apply Nat.lt_succ_diag_r].
  destruct (inp2 m).
  apply Qeq_plus_compat.
  apply IH; intros id H1; apply H; now apply Nat.lt_lt_succ_r.
  apply Qeq_refl.
  apply IH; intros id H1; apply H; now apply Nat.lt_lt_succ_r.
Qed.



Lemma nextneuron_equiv : forall n1 n2 inp len,
    EquivNeuron n1 n2 len ->
    EquivNeuron (NextNeuron inp len n1) (NextNeuron inp len n2) len.
Proof.
  intros n1 n2 inp len [H1 [H2 H3]].
  repeat split; try solve [rewrite ! next_neuro_same_feature; apply H1]; destruct H1 as [Ha [Hb [Hc Hd]]].
  - unfold NextNeuron, Output at 1 3.
    rewrite H2.
    f_equal.
    rewrite 2 nextoutput_nextpotential.
    apply Qeq_bool_equiv; trivial.
    apply Qeq_plus_compat.
    now apply potential_equiv_weight.
    rewrite (Qeq_bool_equiv _ _ _ _ Hd H3).
    destruct (Tau (Feature n2) <=? CurPot n2).
    apply Qeq_refl.
    now apply Qeq_mul_compat.
  - unfold NextNeuron, CurPot.
    unfold NextPotential.
    rewrite (Qeq_bool_equiv _ _ _ _ Hd H3).
    destruct (Tau (Feature n2) <=? CurPot n2).
    now apply potential_equiv_weight.
    apply Qeq_plus_compat.
    now apply potential_equiv_weight.
    now apply Qeq_mul_compat.
Qed.


Lemma nextneuron_equiv_inp : forall n inp1 inp2 len,
    (forall x, (x < len)%nat -> inp1 x = inp2 x) ->
    EquivNeuron (NextNeuron inp1 len n) (NextNeuron inp2 len n) len.
Proof.
  intros n1 inp1 inp2 len H1.
  repeat split.
  - unfold NextNeuron, Output at 1 3.
    f_equal.
    rewrite 2 nextoutput_nextpotential.
    apply Qeq_bool_equiv_r.
    apply Qplus_inj_r.
    now apply potential_equiv_inp.
  - unfold NextNeuron, CurPot.
    unfold NextPotential.
    destruct (Tau (Feature n1) <=? CurPot n1).
    now apply potential_equiv_inp.
    apply Qplus_inj_r.
    now apply potential_equiv_inp.
Qed.


Lemma afternstepsneuron_equiv : forall n1 n2 inp len,
    EquivNeuron n1 n2 len ->
    EquivNeuron (AfterNstepsNeuron n1 inp len) (AfterNstepsNeuron n2 inp len) len.
Proof.
  intros n1 n2 inp len H.
  induction inp as [|i inp IH]; trivial.
  simpl.
  now apply nextneuron_equiv.
Qed.



Lemma afternstepsneuron_equiv_inp : forall n inp1 inp2 len,
    (forall i1 i2 l1 l2 l3 l4,
        inp1 = l1 ++ i1 :: l2 ->
        inp2 = l3 ++ i2 :: l4 ->
        length l1 = length l3 ->
        forall x, (x < len)%nat -> i1 x = i2 x) ->
     length inp1 = length inp2 ->       
    EquivNeuron (AfterNstepsNeuron n inp1 len) (AfterNstepsNeuron n inp2 len) len.
Proof.
  intros n inp1 inp2 len.
  revert n inp2.
  induction inp1 as [|i1 inp1 IH]; intros n [|i2 inp2] H H0; simpl; inversion H0; trivial.
  apply (EquivNeuron_refl n len).

  specialize (H i1 i2 [] inp1 [] inp2 (eq_refl _) (eq_refl _) (eq_refl _)) as H1.
  apply (nextneuron_equiv_inp (AfterNstepsNeuron n inp1 len)) in H1.
  apply (EquivNeuron_trans _ _ _ _ H1).
  apply nextneuron_equiv.
  apply IH; trivial.
  intros i1' i2' l1 l2 l3 l4 H3 H4 H5.
  subst.
  apply (H _ _ (i1 :: l1) l2 (i2 :: l3) l4); trivial.
  simpl.
  now rewrite H5.
Qed.


(*** One-input or two-inputs-neuron ***)

Definition One_Input_Or_Less (nf : NeuronFeature) id len :=  
  (id < len)%nat /\
    (forall id', id <> id' -> (id' < len)%nat ->
                 Weights nf id' == 0).


Definition Two_Inputs_Or_Less (nf : NeuronFeature) id1 id2 len :=
  (id1 < len)%nat /\
    (id2 < len)%nat /\
    id1 <> id2 /\  
    (forall id', id1 <> id' -> id2 <> id' -> (id' < len)%nat ->
                 Weights nf id' == 0).



Lemma Two_Inputs_One : forall nf id len,
    Two_Inputs_Or_Less nf len id (S len) ->
    One_Input_Or_Less nf id len.
Proof.
  intros nf id len [H0 [H1 [H2 H3]]].
  split.
  - apply not_eq_sym in H2.
    now apply nat_lt_S_non_eq_n.
  - intros id' H4 H5.
    apply H3; trivial.
    apply not_eq_sym.
    now apply Nat.lt_neq.
    now apply Nat.lt_lt_succ_r.
Qed.


Lemma One_input_len : forall nf id len,
    One_Input_Or_Less nf id len -> (0 < len)%nat.
Proof.
  intros nf id len [H].
  now apply Nat.lt_lt_0 in H.
Qed.


Lemma One_input_S : forall nf id len,
    One_Input_Or_Less nf id (S len) ->
    id <> len ->
    One_Input_Or_Less nf id len.
Proof.
  intros nf id len [Hidlen Hid'] H0.
  repeat split; trivial.
  - apply PeanoNat.lt_n_Sm_le in Hidlen.
    apply Nat.le_lteq in Hidlen as [Hidlen|Hidlen]; trivial; now destruct H0.
  - intros id' H1 H2.
    apply Hid'; trivial.
    now apply Nat.lt_lt_succ_r.
Qed.


Lemma Two_Inputs_S : forall nf id1 id2 len,
    Two_Inputs_Or_Less nf id1 id2 (S len) ->
    id1 <> len ->
    id2 <> len ->
    Two_Inputs_Or_Less nf id1 id2 len.
Proof.
  intros nf id1 id2 len [H0 [H1 [H2 H3]]].
  repeat split; trivial.
  - now apply nat_lt_S_non_eq_n.
  - now apply nat_lt_S_non_eq_n.
  - intros id' H5 H6 H7.
    apply H3; trivial.
    now apply Nat.lt_lt_succ_r.
Qed.


Lemma Two_Inputs_sym : forall nf id1 id2 len,
    Two_Inputs_Or_Less nf id1 id2 len ->
    Two_Inputs_Or_Less nf id2 id1 len.
Proof.
  intros nf id1 id2 len [H0 [H1 [H2 H3]]].
  repeat split; trivial.
  now apply not_eq_sym.
  intros id' H4 H5 H6.
  now apply H3.
Qed.


Lemma One_input_EquivNeuron : forall nf1 nf2 id len,
    EquivFeature nf1 nf2 len ->
    One_Input_Or_Less nf1 id len ->
    One_Input_Or_Less nf2 id len.
Proof.
  intros nf1 nf2 id len [_ [H _]] [Hoi1 Hoi2].
  split; trivial.
  intros id' H1 H2.
  specialize (H _ H2).
  apply Qeq_sym in H.
  apply (Qeq_trans _ _ _ H).
  now apply Hoi2.
Qed.


Lemma One_input_Alw_Pos : forall m nf id len,
    One_Input_Or_Less nf id len ->
    Tau nf <= Weights nf id->
    (id <= m <= len)%nat ->
    forall id0 : nat, (id0 < m)%nat -> 0 <= Weights nf id0.
Proof.
  intros m nf id len [Hlenid Hid'] H Hm id0 H0.
  case_eq (id =? id0)%nat; intros H1.
  - apply Nat.eqb_eq in H1.
    subst.
    revert H.
    apply Qle_trans.
    apply Qlt_le_weak.
    apply nf.
  - apply Nat.eqb_neq in H1.
    apply Qle_lteq.
    right.
    apply Qeq_sym.
    apply Hid'; trivial.
    destruct Hm as [_ Hm].
    revert H0 Hm. apply Nat.lt_le_trans.
Qed.



(** Properties of the function potential **)

Lemma potential_nneg_w : forall inp w len,
    (forall id, (id < len)%nat -> 0 <= w id) ->
    0 <= potential w inp len.
Proof.
  intros inp w len.
  induction len as [|m IH]; intros H; [apply Qle_refl|].
  simpl.
  case_eq (inp m); intros H0.
  - rewrite <- plusQ_0.
    apply Qplus_le_compat.
    apply IH.
    intros id H1.
    apply H.
    now apply Nat.lt_lt_succ_r.
    apply H.
    apply Nat.lt_succ_diag_r.
  - apply IH.
    intros id H1.
    apply H.
    now apply Nat.lt_lt_succ_r.
Qed.


Lemma potential_npos_w : forall w inp len,
    (forall x, (x < len)%nat -> w x <= 0) ->
    potential w inp len <= 0.
Proof.
  intros w inp len H.
  induction len as [|m IH]; [apply Qle_refl|].
  simpl.
  case_eq (inp m); intros Hm.
  - rewrite <- plusQ_0.
    apply Qplus_le_compat.
    apply IH.
    intros x H1.
    apply H; trivial.
    now apply Nat.lt_lt_succ_r.
    apply H.
    apply Nat.lt_succ_diag_r.
  - apply IH.
    intros x H1.
    apply H; trivial.
    now apply Nat.lt_lt_succ_r.
Qed.





(* One input *)

Lemma potential_no_i : forall nf inp len,
    (forall id : nat, (id < len)%nat -> Weights nf id == 0) ->
    potential (Weights nf) inp len == 0.
Proof.
  intros nf inp len H.
  induction len as [|m IH]; trivial.
  apply Qeq_refl.
  simpl.
  destruct (inp m).
  - apply (Qeq_trans _ (0 + Weights nf m)).
    apply Qplus_inj_r.
    apply IH.
    intros id Hid.
    apply H.
    now apply Nat.lt_lt_succ_r.
    apply Qeq_plus_0_r_eq.
    apply H.
    apply Nat.lt_succ_diag_r.
  - apply IH.
    intros id Hid.
    apply H.
    now apply Nat.lt_lt_succ_r.
Qed.


Lemma potential_oi : forall nf id inp len,
    One_Input_Or_Less nf id len ->
    potential (Weights nf) inp len ==
      if inp id
      then Weights nf id
      else 0.
Proof.
  intros nf id inp len H.
  induction len as [|m IH]; trivial.
  destruct H as [H _].
  now apply Nat.nlt_0_r in H.
  simpl.
  case_eq (id =? m)%nat; intros H0.
  - apply Nat.eqb_eq in H0.
    subst.
    assert (potential (Weights nf) inp m == 0).
    apply potential_no_i.
    intros id Hid.
    apply H.
    apply Nat.lt_neq in Hid.
    now apply not_eq_sym.
    now apply Nat.lt_lt_succ_r.
    destruct (inp m); trivial.
    apply (Qeq_trans _ (0 + Weights nf m)).
    now apply Qplus_inj_r.
    apply Qplus_0_l.
  - apply Nat.eqb_neq in H0.
    specialize (IH (One_input_S _ _ _ H H0)).
    destruct (inp m); trivial.
    apply (Qeq_trans _ (potential (Weights nf) inp m + 0)).
    apply Qplus_inj_l.
    apply H; trivial.
    apply Nat.lt_succ_diag_r.
    now apply Qeq_plus_0_l_eq.
Qed.



Lemma potential1N_w_greater_n : forall m id inp (nf: NeuronFeature) len,
    One_Input_Or_Less nf id len ->
    m <= Weights nf id ->
    0 < m ->
    (m <=? potential (Weights nf) inp len) = inp id.
Proof.
  intros m id inp nf len Hoi H H1.
  rewrite (Qeq_bool_equiv_r _ _ _ (potential_oi _ _ _ _ Hoi)).
  destruct (inp id).
  now apply Qle_bool_iff.
  now apply Qleb_lt.
Qed.


Lemma potential1N_w_less_n: forall m id inp (nf: NeuronFeature) len,
    One_Input_Or_Less nf id len ->
    Weights nf id < m ->
    0 < m ->
    (m <=? potential (Weights nf) inp len) = false.
Proof.
  intros m id inp nf len Hoi H H1.
  rewrite (Qeq_bool_equiv_r _ _ _ (potential_oi _ _ _ _ Hoi)).
  destruct (inp id); apply Qleb_lt; trivial.
Qed.




(* Two inputs *)

Lemma potential_ti : forall nf id1 id2 inp len,
    Two_Inputs_Or_Less nf id1 id2 len ->
    potential (Weights nf) inp len ==
      (if inp id1
       then Weights nf id1
       else 0) + (if inp id2
                  then Weights nf id2
                  else 0).
Proof.
  intros nf id1 id2 inp len Hti.
  induction len as [|m IH].
  - destruct (Nat.nlt_0_r id1).
    apply Hti.
  - simpl.
    destruct (Nat.eq_dec id1 m) as [Hidm|Hidm].
    * subst.
      apply Two_Inputs_One in Hti.
      destruct (inp m); [apply (fun H => Qeq_trans _ _ _ H (Qplus_comm _ _)); apply Qplus_inj_r|apply (fun H => Qeq_trans _ _ _ H (Qeq_sym _ _ (Qplus_0_l _)))]; now apply potential_oi.
    * destruct (Nat.eq_dec id2 m) as [Hid2m|Hid2m].
      -- subst.
         apply Two_Inputs_sym in Hti.
         apply Two_Inputs_One in Hti.
         destruct (inp m); [apply Qplus_inj_r|apply (fun H => Qeq_trans _ _ _ H (Qeq_sym _ _ (Qplus_0_r _)))]; now apply potential_oi.
      -- apply Two_Inputs_S in Hti as H; trivial.
         apply IH in H.
         case_eq (inp m); intros H0; [apply (fun H => Qeq_trans _ _ _ H (Qplus_0_r _)); apply Qeq_plus_compat|]; trivial.
         apply Hti; trivial.
         apply Nat.lt_succ_diag_r.
Qed.


(** Link between CurPot and Output for AfterNstepNeuron **)


Lemma AfterNstepsNeuron_curpot_cons : forall n i inp len,
    CurPot (AfterNstepsNeuron n (i :: inp) len) ==
      potential (Weights (Feature n)) i len +
        (if
            Tau (Feature n) <=?
              CurPot
                (AfterNstepsNeuron n inp len)
          then 0
          else
            Leak_Factor (Feature n) *
              CurPot (AfterNstepsNeuron n inp len)).
Proof.
  intros n i inp len.
  simpl.
  unfold NextPotential.
  rewrite after_nsteps_same_feature.
  destruct (Tau (Feature n) <=? CurPot (AfterNstepsNeuron n inp len)).
  apply Qeq_sym.
  apply Qplus_0_r.
  apply Qeq_refl.
Qed.


Lemma AfterNSN_curpot_output_unfold : forall i (inp: list (nat -> bool)) n len,
    Output (AfterNstepsNeuron n (i :: inp) len) = (Tau (Feature n) <=? CurPot (AfterNstepsNeuron n (i :: inp) len)) :: Output (AfterNstepsNeuron n inp len).
Proof.
  intros i inp n len.
  rewrite <- (after_nsteps_same_feature (i :: inp) n len).
  now rewrite CurPot_Output.
Qed.


Lemma AfterNSN_curpot_output_true : forall i (inp: list (nat -> bool)) n len,
    Tau (Feature n) <= CurPot (AfterNstepsNeuron n (i :: inp) len) <->
      Output (AfterNstepsNeuron n (i :: inp) len) = true :: Output (AfterNstepsNeuron n inp len).
Proof.
  intros i inp n len.
  split; intros H.
  - rewrite AfterNSN_curpot_output_unfold.
    apply Qle_bool_iff in H.
    now rewrite H.
  - rewrite AfterNSN_curpot_output_unfold in H.
    inversion H.
    now apply Qle_bool_iff.
Qed.


Lemma AfterNSN_curpot_output_false : forall i (inp: list (nat -> bool)) n len,
    CurPot (AfterNstepsNeuron n (i :: inp) len) < Tau (Feature n) <->
      Output (AfterNstepsNeuron n (i :: inp) len) = false :: Output (AfterNstepsNeuron n inp len).
Proof.
  intros i inp n len.
  split; intros H.
  - rewrite AfterNSN_curpot_output_unfold.
    apply Qleb_lt in H.
    now rewrite H.
  - rewrite AfterNSN_curpot_output_unfold in H.
    inversion H.
    now apply Qleb_lt.
Qed.


(*** Properties for SetNeuron ***)

Definition is_initial_neuro n len := exists (nf: NeuronFeature), EquivNeuron n (SetNeuron nf) len.


Lemma is_initial_neuro_curpot : forall n len,
    is_initial_neuro n len -> CurPot n == 0.
Proof.
  intros n len [nf [_ [_ Hinit]]]; trivial.
Qed.


Lemma is_initial_neuro_output : forall n len,
    is_initial_neuro n len -> Output n = [false].
Proof.
  intros n len [nf [_ [Hinit _]]]; trivial.
Qed.



Lemma CurPot_cons_oi : forall id i inp n len,
    One_Input_Or_Less (Feature n) id len ->
    CurPot (AfterNstepsNeuron n (i :: inp) len) ==
      (if i id
      then Weights (Feature n) id
      else 0) + (if Tau (Feature n) <=? CurPot (AfterNstepsNeuron n inp len)
   then 0
   else Leak_Factor (Feature n) * CurPot (AfterNstepsNeuron n inp len)).
Proof.
  intros id i inp n len Hoi.
  revert i.
  induction inp as [|i' inp IH]; intros i.
  - rewrite AfterNstepsNeuron_curpot_cons.
    simpl.
    apply Qplus_inj_r.
    now apply potential_oi.
  - rewrite AfterNstepsNeuron_curpot_cons.
    apply Qplus_inj_r.
    now apply potential_oi.
Qed.



Lemma CurPot_cons_w_greater_tau_oi : forall id i inp n len,
    One_Input_Or_Less (Feature n) id len ->
    Tau (Feature n) <= Weights (Feature n) id ->
    is_initial_neuro n len ->
    CurPot (AfterNstepsNeuron n (i :: inp) len) ==
      if i id
      then Weights (Feature n) id
      else 0.
Proof.
  intros id i inp n len Hoi H Hinit.
  revert i.
  induction inp as [|i' inp IH]; intros i.
  - apply is_initial_neuro_curpot in Hinit.
    apply (Qeq_trans _ _ _ (CurPot_cons_oi _ _ _ _ _ Hoi)).
    simpl.
    rewrite ! (Qeq_bool_equiv_r _ _ _ Hinit).
    apply Qeq_sym.
    apply Qeq_plus_0_l_eq.
    apply Qplus_inj_l; apply Qeq_sym.
    rewrite if_false_r; [|apply Qleb_lt; apply (Feature n)].
    apply mul_0_iff.
    now right.
  - apply (Qeq_trans _ _ _ (CurPot_cons_oi _ _ _ _ _ Hoi)).
    apply Qeq_sym.
    apply Qeq_plus_0_l_eq.
    apply Qplus_inj_l; apply Qeq_sym.
    case_eq (Tau (Feature n) <=? CurPot (AfterNstepsNeuron n (i' :: inp) len)); intros H0.
    apply Qeq_refl.
    apply mul_0_iff.
    right.
    rewrite IH.
    case_eq (i' id); intros H1; [|apply Qeq_refl].
    rewrite ! (Qeq_bool_equiv_r _ _ _ (IH _)), H1 in H0.
    apply Qle_bool_iff in H.
    rewrite H0 in H.
    inversion H.
Qed.



Lemma Output_cons_w_greater_tau_oi : forall id i inp n len,
    One_Input_Or_Less (Feature n) id len ->
    Tau (Feature n) <= Weights (Feature n) id ->
    is_initial_neuro n len ->
    Output (AfterNstepsNeuron n (i :: inp) len) = i id :: Output (AfterNstepsNeuron n inp len).
Proof.
  intros id i inp n len Hoi H Hinit.
  rewrite AfterNSN_curpot_output_unfold.
  f_equal.
  rewrite (Qeq_bool_equiv_r _ _ _ (CurPot_cons_w_greater_tau_oi _ _ _ _ _ Hoi H Hinit)).
  case_eq (i id); intros H1.
  now apply Qle_bool_iff.
  apply Qleb_lt.
  apply (Feature n).
Qed.




(* Properties for multiple inputs neurons *)

(* Always Non Negative : CurPot is non negative if all weights are positive *)

Lemma Always_N_Neg: forall (inp: list (nat -> bool)) (n : Neuron) len,
    (forall id, (id < len)%nat -> 0 <= Weights (Feature n) id) ->
    is_initial_neuro n len ->
    0 <= (CurPot (AfterNstepsNeuron n inp len)).
Proof.
  induction inp as [|h t]; intros n len H Hinit; [apply is_initial_neuro_curpot in Hinit; apply Qeq_sym in Hinit; revert Hinit; apply Qle_eq_r; apply Qle_refl|].
  apply (fun H => Qle_eq_r _ _ _ H (Qeq_sym _ _ (AfterNstepsNeuron_curpot_cons _ _ _ _))).
  simpl.
  destruct (Tau (Feature n) <=? CurPot (AfterNstepsNeuron n t len)).
  - apply (fun H => Qle_eq_r _ _ _ H (Qeq_sym _ _ (Qplus_0_r _))).
    now apply potential_nneg_w.
  - rewrite <- plusQ_0.
    apply Qplus_le_compat.
    * now apply potential_nneg_w.
    * apply Qmult_le_0_compat.
      apply LeakRange.
      now apply IHt.
Qed.


(*Inhibitor effect for multiple inputs*)

Lemma Inhibit_Ineg : forall inp n len,
    (forall x : nat, (x < len)%nat -> Weights (Feature n) x <= 0) ->
    (Tau (Feature n) <=? potential (Weights (Feature n)) inp len) = false.
Proof.
  intros inp n len Hw.
  apply Qleb_lt.
  apply (Qle_lt_trans _ 0).
  now apply potential_npos_w.
  apply (Feature n).
Qed.



Theorem Inhibitor_Effect : forall inp n len,
    (forall x : nat, (x < len)%nat -> Weights (Feature n) x <= 0) ->
    is_initial_neuro n len ->
    forall a,
      In a
         (Output (AfterNstepsNeuron n inp len)) ->
      a = false.
Proof.
  intros inp n len H Hinit a Hout.
  induction inp as [|i inp IH].
  - apply is_initial_neuro_output in Hinit.
    simpl in Hout.
    rewrite Hinit in Hout.
    destruct Hout as [Hout|Hout].
    now subst.
    inversion Hout.
  - rewrite AfterNSN_curpot_output_unfold in Hout.
    destruct Hout as [Hout|Hout].
    * subst.
      rewrite (Qeq_bool_equiv_r _ _ _ (AfterNstepsNeuron_curpot_cons _ _ _ _)).
      case_eq (Tau (Feature n) <=?
                 CurPot
                   (AfterNstepsNeuron n inp len)); intros Hcur.
      -- rewrite Qeq_bool_equiv_0_r.
         now apply Inhibit_Ineg.
      -- apply Qleb_lt.
         apply Qlt_inf_0_trans_l.
         ** now apply potential_npos_w.
         ** apply Qmul_0_1_lt; try apply (Feature n).
            now apply Qleb_lt.
    * now apply IH in Hout.
Qed.


(** Properties for one-input neuron **)

(* Property : Delayer Effect *)


Theorem Delayer_Effect : forall id inp n len,
    One_Input_Or_Less (Feature n) id len ->
    Tau (Feature n) <= Weights (Feature n) id->
    is_initial_neuro n len ->
    Output (AfterNstepsNeuron n inp len) = (map (fun f => f id) inp) ++ [false].
Proof.
  intros id inp n len Hoi Htau Hinit.
  induction inp as [|i inp IH]; [now apply is_initial_neuro_output in Hinit|].
  now rewrite (Output_cons_w_greater_tau_oi _ _ _ _ _ Hoi Htau Hinit), IH.
Qed.


(* Property : Filtering Effect *)

Lemma Filtering_Effect_Head : forall id inp n len,
    One_Input_Or_Less (Feature n) id len ->
    Weights (Feature n) id < Tau (Feature n) ->
    is_initial_neuro n len ->
    forall a1 a2 l,
      Output (AfterNstepsNeuron n inp len) = a1 :: a2 :: l -> a1 && a2 = false.
Proof.
  intros id inp n len Hoi H Hinit a1 a2 l H0.
  destruct inp as [|i1 [|i2 inp]].
  - apply is_initial_neuro_output in Hinit; simpl in H0; rewrite Hinit in H0; inversion H0.
  - inversion H0; apply is_initial_neuro_output in Hinit; simpl in H3; rewrite Hinit in H3; inversion H3; apply andb_false_r.
  - rewrite 2 AfterNSN_curpot_output_unfold in H0.
    rewrite (Qeq_bool_equiv_r _ _ _ (AfterNstepsNeuron_curpot_cons _ _ _ _)) in H0.
    case_eq (Tau (Feature n) <=? CurPot (AfterNstepsNeuron n (i2::inp) len)); intros H1; rewrite H1 in H0; inversion H0.
    * rewrite Qeq_bool_equiv_0_r, andb_true_r.
      apply (potential1N_w_less_n _ _ _ _ _ Hoi); [trivial|apply (Feature n)].
    * apply andb_false_r.
Qed.


Theorem Filtering_Effect : forall id inp n len,
    One_Input_Or_Less (Feature n) id len ->
    Weights (Feature n) id < Tau (Feature n) ->
    is_initial_neuro n len ->
    forall a1 a2 l1 l2,
      Output (AfterNstepsNeuron n inp len) = l1 ++ a1 :: a2 :: l2 -> a1 && a2 = false.
Proof.
  intros id inp n len Hoi.
  intros H Hinit a1 a2 l1 l2 Hout.
  revert inp Hout.
  induction l1 as [|hd1 tl1 IH]; intros inp Hout.
  - simpl in Hout.
    revert Hout; apply (Filtering_Effect_Head _ _ _ _ Hoi H Hinit).
  - destruct inp as [|i inp].
    * apply is_initial_neuro_output in Hinit.
      simpl in Hout.
      rewrite Hinit in Hout.
      rewrite app_comm_cons in Hout.
      now apply one_elt_list_not_two in Hout.
    * inversion Hout.
      now apply IH in H2.
Qed.


(* Property : Behaviour of the output of a one-input neuron *)


Theorem One_input_generic : forall id inp n len,
    One_Input_Or_Less (Feature n) id len ->
    is_initial_neuro n len ->
Output (AfterNstepsNeuron n inp len) = (map (fun f => f id) inp) ++ [false] \/
      forall a1 a2 l1 l2,
        Output (AfterNstepsNeuron n inp len) = l1 ++ a1 :: a2 :: l2 -> a1 && a2 = false.
Proof.
  intros id inp n len Hoi Hinit.
  case_eq (Tau (Feature n) <=? Weights (Feature n) id); intros Htau.
  - left.
    apply Qle_bool_iff in Htau.
    now apply Delayer_Effect.
  - right.
    apply Qleb_lt in Htau.
    now apply (Filtering_Effect id).
Qed.


(* Property : Spike-Decreasing effect *)

Lemma inp_0_Output_0 : forall id n len i inp,
    One_Input_Or_Less (Feature n) id len ->
    is_initial_neuro n len ->
    i id = false ->
    Output (AfterNstepsNeuron n (i :: inp) len) = false :: Output (AfterNstepsNeuron n inp len).
Proof.
  intros id n len i inp Hoi Hinit Hid.
  rewrite AfterNSN_curpot_output_unfold.
  rewrite ! (Qeq_bool_equiv_r _ _ _ (CurPot_cons_oi _ _ _ _ _ Hoi)).
  f_equal.
  rewrite Hid.
  rewrite (Qeq_bool_equiv_r _ _ _ (Qplus_0_l _)).
  case_eq (Tau (Feature n) <=? CurPot (AfterNstepsNeuron n inp len)); intros H0.
  - apply Qleb_lt.
    apply (Feature n).
  - apply Qleb_lt.
    apply Qmul_0_1_lt; try apply (Feature n).
    now apply Qleb_lt.
Qed.


Theorem Spike_Decreasing : forall id inp n len,
    One_Input_Or_Less (Feature n) id len ->
    is_initial_neuro n len ->
  (count_occ bool_dec (Output (AfterNstepsNeuron n inp len)) true <= count_occ bool_dec (map (fun f => f id) inp) true)%nat.
Proof.
  intros id inp n len Hoi Hinit.
  induction inp as [|i inp IH]; [apply is_initial_neuro_output in Hinit; simpl; rewrite Hinit; apply Nat.le_refl|].
  case_eq (i id); intros Hhd.
  - rewrite AfterNSN_curpot_output_unfold, map_cons.
    case_eq (Qle_bool (Tau (Feature n))
        (CurPot (AfterNstepsNeuron n (i :: inp) len))); intros H.
    * rewrite ! (count_occ_cons_eq bool_dec); trivial.
      apply le_n_S.
      apply IH.    
    * rewrite count_occ_cons_neq; [|discriminate].
      rewrite (count_occ_cons_eq bool_dec); trivial.
      simpl.
      apply le_S.
      apply IH.
  - rewrite (inp_0_Output_0 _ _ _ _ _ Hoi Hinit Hhd), map_cons, Hhd.
    rewrite ! count_occ_cons_neq; try discriminate.
    apply IH.
Qed.

