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
Require Import Facts Neuron Circuit.


(** Archetypes **)


(* Archetype of Simple Series and Series with multiples outputs *)

Record Series (c : NeuroCircuit) :=
  Make_Series
    {
      OneSupplementS : SupplInput c = 1%nat;
      ExistsNeuronS : (0 < length (ListNeuro c))%nat;
      FirstNeuronS : forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 0%nat ->
        (forall id' : nat, (id' < length (ListNeuro c))%nat -> Weights (Feature n) id' == 0) /\
          0 < Weights (Feature n) (length (ListNeuro c));
      UniqueWeightS :
      forall n m,
        In n (ListNeuro c) ->
        Id (Feature n) = S m ->
        (forall id' : nat, m <> id' -> (id' < length (ListNeuro c) + 1)%nat -> Weights (Feature n) id' == 0) /\
          0 < Weights (Feature n) m
    }.


(* Archetype of Parallel composition *)

Record ParallelComposition (c : NeuroCircuit) :=
  Make_ParaComp
    {
      OneSupplementPC : SupplInput c = 1%nat;
      ExistsNeuronPC : (0 < length (ListNeuro c))%nat;
      FirstNeuronPC : forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 0%nat ->
        (forall id' : nat, (id' < length (ListNeuro c))%nat -> Weights (Feature n) id' == 0) /\
          0 < Weights (Feature n) (length (ListNeuro c));
      N1NmPC :
      forall n m,
        In n (ListNeuro c) ->
        Id (Feature n) = S m ->
        (forall id' : nat, 0%nat <> id' -> (id' < length (ListNeuro c) + 1)%nat -> Weights (Feature n) id' == 0) /\
          0 < Weights (Feature n) 0%nat
    }.


(* Archetype of Positive Loop *)

Record PositiveLoop (c : NeuroCircuit) :=
  Make_PosLoop
    {
      OneSupplementPL : SupplInput c = 1%nat;
      ListNeuroLengthPL : length (ListNeuro c) = 2%nat;
      FirstNeuronPL : forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 0%nat ->
        0 < Weights (Feature n) 1%nat /\
          0 < Weights (Feature n) 2%nat;
      SecondNeuroPL :
      forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 1%nat ->
        0 < Weights (Feature n) 0%nat /\
          Weights (Feature n) 2%nat == 0;
    }.


(* Archetype of Negative Loop *)

Record NegativeLoop (c : NeuroCircuit) :=
  Make_NegLoop
    {
      OneSupplementNL : SupplInput c = 1%nat;
      ListNeuroLengthNL : length (ListNeuro c) = 2%nat;
      FirstNeuronNL : forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 0%nat ->
        Weights (Feature n) 1%nat < 0 /\
          0 < Weights (Feature n) 2%nat;
      SecondNeuroNL :
      forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 1%nat ->
        0 < Weights (Feature n) 0%nat /\
          Weights (Feature n) 2%nat == 0;
    }.


(* Archetype of Inhibition *)

Record Inhibition (c : NeuroCircuit) :=
  Make_Inhib
    {
      OneSupplementI : SupplInput c = 2%nat;
      ListNeuroLengthI : length (ListNeuro c) = 2%nat;
      FirstNeuronI : forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 0%nat ->
        Weights (Feature n) 1%nat == 0 /\
          0 < Weights (Feature n) 2%nat /\
          Weights (Feature n) 3%nat == 0;
      SecondNeuroI :
      forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 1%nat ->
        Weights (Feature n) 0%nat < 0 /\
          Weights (Feature n) 2%nat == 0 /\
          0 < Weights (Feature n) 3%nat;
    }.


(* Archetype of Contralateral Inhibition *)

Record ContraInhib (c : NeuroCircuit) :=
  Make_ContrInhib
    {
      OneSupplementCI : SupplInput c = 2%nat;
      ListNeuroLengthCI : length (ListNeuro c) = 2%nat;
      FirstNeuronCI : forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 0%nat ->
        Weights (Feature n) 1%nat < 0 /\
          0 < Weights (Feature n) 2%nat /\
          Weights (Feature n) 3%nat == 0;
      SecondNeuroCI :
      forall n,
        In n (ListNeuro c) ->
        Id (Feature n) = 1%nat ->
        Weights (Feature n) 0%nat < 0 /\
          Weights (Feature n) 2%nat == 0 /\
          0 < Weights (Feature n) 3%nat;
    }.




(** One input : **)

(* Series *)


Lemma Series_One_Input_Or_Less_0 : forall n1 nc,
    Series nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    One_Input_Or_Less (Feature n1) (length (ListNeuro nc)) (length (ListNeuro nc) + SupplInput nc).
Proof.
  intros n1 nc Hserie Hin Hid.
  apply IdInfLen in Hin as Hlen.
  split.
  - rewrite (OneSupplementS _ Hserie).
    rewrite Nat.add_1_r.
    apply Nat.lt_succ_diag_r.
  - intros id' Hid1 Hid2.
    rewrite (OneSupplementS _ Hserie) in Hid2.
    apply (FirstNeuronS _ Hserie _ Hin Hid).
    apply nat_lt_S_non_eq_n; [now rewrite Nat.add_1_r in Hid2|now apply not_eq_sym].
Qed.
   
   
Lemma Series_One_Input_Or_Less_succ : forall n1 n2 nc,
    Series nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = S n2 ->
    One_Input_Or_Less (Feature n1) n2 (length (ListNeuro nc) + SupplInput nc).
Proof.
  intros n1 n2 nc Hserie Hin Hid.
  apply IdInfLen in Hin as Hlen.
  split.
  - rewrite Hid in Hlen.
    apply (Nat.lt_trans _ (S n2)).
    apply Nat.lt_succ_diag_r.
    now apply Nat.lt_lt_add_r.
  - intros id Hid1 Hid2.
    rewrite (OneSupplementS _ Hserie) in Hid2.
    now apply (UniqueWeightS _ Hserie _ _ Hin Hid).
Qed.


(* Parallel Composition *)


Lemma ParalComp_One_Input_Or_Less_0 : forall n1 nc,
    ParallelComposition nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    One_Input_Or_Less (Feature n1) (length (ListNeuro nc)) (length (ListNeuro nc) + SupplInput nc).
Proof.
  intros n1 nc Hpc Hin Hid.
  apply IdInfLen in Hin as Hlen.
  split.
  - rewrite (OneSupplementPC _ Hpc).
    rewrite Nat.add_1_r.
    apply Nat.lt_succ_diag_r.
  - rewrite (OneSupplementPC _ Hpc).
    intros id' Hid1 Hid2.
    apply (FirstNeuronPC _ Hpc _ Hin Hid).
    apply nat_lt_S_non_eq_n; [now rewrite Nat.add_1_r in Hid2|now apply not_eq_sym].
Qed.


Lemma ParalComp_One_Input_Or_Less_succ : forall n1 n2 nc,
    ParallelComposition nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = S n2 ->
    One_Input_Or_Less (Feature n1) 0%nat (length (ListNeuro nc) + SupplInput nc).
Proof.
  intros n1 n2 nc Hpc Hin Hid.
  apply IdInfLen in Hin as Hlen.
  split.
  - rewrite Hid in Hlen.
    apply (Nat.lt_trans _ (S n2)).
    apply Nat.lt_0_succ.
    now apply Nat.lt_lt_add_r.
  - rewrite (OneSupplementPC _ Hpc). 
    now apply (N1NmPC _ Hpc _ n2 Hin Hid).
Qed.


(* Positive Loop *)


Lemma One_Input_Or_Less_PL_1 : forall nc n1 n2,
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    PositiveLoop nc ->
    One_Input_Or_Less (Feature n2) (Id (Feature n1))
                      (length (ListNeuro nc) + SupplInput nc).
Proof.
  intros nc n1 n2 Hid1 Hin2 Hid2 HPos.
  split.
  rewrite Hid1.
  rewrite ListNeuroLengthPL, OneSupplementPL; trivial.
  apply Nat.lt_0_succ.
  intros id' Hid1' Hid'.
  rewrite ListNeuroLengthPL, OneSupplementPL in Hid'; trivial.
  apply PeanoNat.lt_n_Sm_le in Hid'.
  destruct id' as [|[|[|m]]].
  now destruct Hid1'.
  rewrite <- Hid2.
  rewrite WId.
  apply Qeq_refl.
  apply (proj2 (SecondNeuroPL _ HPos _ Hin2 Hid2)).
  do 2 apply PeanoNat.lt_S_n in Hid'.
  now destruct (Nat.nlt_0_r m).
Qed.


(* Negative Loop *)

Lemma One_Input_Or_Less_NL_1 : forall nc n1 n2,
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    NegativeLoop nc ->
    One_Input_Or_Less (Feature n2) (Id (Feature n1))
                      (length (ListNeuro nc) + SupplInput nc).
Proof.
  intros nc n1 n2 Hid1 Hin2 Hid2 HPos.
  split.
  rewrite Hid1.
  rewrite ListNeuroLengthNL, OneSupplementNL; trivial.
  apply Nat.lt_0_succ.
  intros id' Hid1' Hid'.
  rewrite ListNeuroLengthNL, OneSupplementNL in Hid'; trivial.
  apply PeanoNat.lt_n_Sm_le in Hid'.
  destruct id' as [|[|[|m]]].
  now destruct Hid1'.
  rewrite <- Hid2.
  rewrite WId.
  apply Qeq_refl.
  apply (proj2 (SecondNeuroNL _ HPos _ Hin2 Hid2)).
  do 2 apply PeanoNat.lt_S_n in Hid'.
  now destruct (Nat.nlt_0_r m).
Qed.



(** Two Inputs **)

(* Two neurons + 1 external input circuits *)

Lemma Two_Inputs_Two_Neurons : forall n1,
    Id (Feature n1) = 0%nat ->
    Two_Inputs_Or_Less (Feature n1) 1 2 3.
Proof.
  intros n1 Hid.
  repeat split; trivial.
  - apply (Nat.succ_lt_mono 0).
    apply Nat.lt_0_2.
  - apply (Nat.succ_lt_mono 1).
    apply Nat.lt_1_2.
  - intros id' H1 H2 H3.
    destruct id' as [|[|[|id']]]; try solve [now destruct (Nat.lt_irrefl 3%nat)|do 3 apply PeanoNat.lt_S_n in H3; now destruct (Nat.nlt_0_r id')].
    rewrite <- Hid, WId.
    apply Qeq_refl.
Qed.


Lemma Two_Inputs_Two_Neurons2 : forall n1,
    Id (Feature n1) = 1%nat ->
    Two_Inputs_Or_Less (Feature n1) 0 2 3.
Proof.
  intros n1 Hid.
  repeat split; trivial.
  - apply Nat.lt_0_succ.
  - apply (Nat.succ_lt_mono 1).
    apply Nat.lt_1_2.
  - intros id' H1 H2 H3.
    destruct id' as [|[|[|id']]]; try solve [now destruct (Nat.lt_irrefl 3%nat)|do 3 apply PeanoNat.lt_S_n in H3; now destruct (Nat.nlt_0_r id')].
    rewrite <- Hid, WId.
    apply Qeq_refl.
Qed.


(* Two neurons + 2 external input circuits *)

Lemma Two_Inputs_Two_Neurons3 : forall n1 n2 nc,
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    Id (Feature n2) = 1%nat ->
    Weights (Feature n1) 3 == 0 ->
    Two_Inputs_Or_Less (Feature n1) (Id (Feature n2)) 2 4.
Proof.
  intros n1 n2 nc Hin1 Hid1 Hid2 Hw.
  rewrite Hid2.
  repeat split; trivial.
  - apply (Nat.succ_lt_mono 0).
    apply Nat.lt_0_succ.
  - apply (Nat.succ_lt_mono 1).
    apply (Nat.succ_lt_mono 0).
    apply Nat.lt_0_succ.
  - intros id' H1 H2 H3.
    destruct id' as [|[|[|[|id']]]]; trivial; try solve [now destruct H1|now destruct H2|now destruct (Nat.lt_irrefl 3%nat)].
    rewrite <- Hid1.
    rewrite WId.
    apply Qeq_refl.
    do 4 apply PeanoNat.lt_S_n in H3.
    now destruct (Nat.nlt_0_r id').
Qed.


Lemma Two_Inputs_Two_Neurons4 : forall n1 n2 nc,
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    Id (Feature n2) = 1%nat ->
    Weights (Feature n2) 2 == 0 ->
    Two_Inputs_Or_Less (Feature n2) (Id (Feature n1)) 3 4.
Proof.
  intros n1 n2 nc Hin1 Hid1 Hid2 Hw.
  rewrite Hid1.
  repeat split; trivial.
  - apply Nat.lt_0_succ.
  - apply (Nat.succ_lt_mono 2).
    apply (Nat.succ_lt_mono 1).
    apply (Nat.succ_lt_mono 0).
    apply Nat.lt_0_succ.
  - intros id' H1 H2 H3.
    destruct id' as [|[|[|[|id']]]]; trivial; try solve [now destruct H1|now destruct H2|now destruct (Nat.lt_irrefl 3%nat)].
    rewrite <- Hid2.
    rewrite WId.
    apply Qeq_refl.
    do 4 apply PeanoNat.lt_S_n in H3.
    now destruct (Nat.nlt_0_r id').
Qed.



(** Delayer Effect **)


(* Series *)

Lemma Series_Output_n_Input_0: forall n inp nc,
    is_initial nc ->
    Series nc ->
    In n (ListNeuro nc) ->
    Id (Feature n) = 0%nat ->
    Tau (Feature n) <= Weights (Feature n) (length (ListNeuro nc)) ->
    output_neuron nc inp 0 =
      map (fun f => f (length (ListNeuro nc))) inp ++ [false].
Proof.
  intros n inp nc Hinit Hserie Hin Hid Htau.
  rewrite <- Hid.
  assert (Hoi := Series_One_Input_Or_Less_0 _ _ Hserie Hin Hid).
  apply One_Input_NC_delay_Ext; trivial.
  rewrite (OneSupplementS _ Hserie).
  rewrite Nat.add_1_r.
  apply Nat.lt_succ_diag_r.
Qed.


Lemma Series_Output_n_Input_succ: forall n id inp nc,
    is_initial nc ->
    Series nc ->
    In n (ListNeuro nc) ->
    Id (Feature n) = S id ->
    Tau (Feature n) <= Weights (Feature n) id ->
    output_neuron nc inp (Id (Feature n)) =
      tl (output_neuron nc inp id) ++ [false].
Proof.
  intros n1 id inp nc Hinit Hserie Hin1 Hid1 Htau.
  apply IdInfLen in Hin1 as H.
  rewrite Hid1 in H.
  apply Nat.lt_succ_l in H.
  apply len_inf_in_listneuro in H as [n2 [Hin2 Hid2]].
  subst.
  apply One_Input_NC_delay_Int; trivial.
  now apply Series_One_Input_Or_Less_succ.
Qed.


Lemma Series_Output_n_Input_succ_delayer: forall n n0 inp nc,
    is_initial nc ->
    Series nc ->
    In n0 (ListNeuro nc) ->
    Id (Feature n0) = 0%nat ->
    Tau (Feature n0) <= Weights (Feature n0) (length (ListNeuro nc)) ->
    (forall m id, In m (ListNeuro nc) ->
                  Id (Feature m) = S id ->
                  Tau (Feature m) <= Weights (Feature m) id) ->
    (S n < (length (ListNeuro nc)))%nat ->
    output_neuron nc inp (S n) =
      if (n <? length inp)%nat 
      then afternlist _ (S n)%nat (map (fun f => f (length (ListNeuro nc))) inp) ++ List.repeat false (S (S n))
      else List.repeat false (S (length inp)).
Proof.
  intros n n0 inp nc Hinit Hserie Hin0 Hid0 Htau0 Htau Hlen.
  induction n as [|m IH].
  - simpl.
    apply len_inf_in_listneuro in Hlen as [n1 [Hin1 Hlen1]].
    rewrite <- Hlen1.
    rewrite (Series_Output_n_Input_succ _ 0); trivial.
    * rewrite (Series_Output_n_Input_0 _ _ _ Hinit Hserie Hin0 Hid0 Htau0).
      destruct inp; trivial.
      rewrite map_cons.
      simpl.
      now rewrite <- app_assoc.
    * now apply Htau.      
  - apply Nat.lt_succ_l in Hlen as Hlen'.
    apply len_inf_in_listneuro in Hlen as [n1 [Hin1 Hlen1]].
    generalize Hlen'; intros Hlen.
    apply len_inf_in_listneuro in Hlen' as [n2 [Hin2 Hlen2]].
    rewrite <- Hlen1.
    specialize (Htau _ _ Hin1 Hlen1). 
    rewrite (Series_Output_n_Input_succ _ (S m)); trivial.
    rewrite IH; trivial.
    rewrite Hlen1.
    case_eq (S m <? length inp)%nat; intro Hm.
    * apply Nat.ltb_lt in Hm.
      apply Nat.lt_succ_l in Hm as Hm'.
      apply Nat.ltb_lt in Hm'.
      rewrite Hm'.
      simpl.
      rewrite afternlist_tl_app.
      rewrite <- app_assoc.
      f_equal.
      now rewrite ! afternlist_tl.
      rewrite <- ! app_comm_cons.
      now rewrite repeat_cons_same.
      destruct inp.
      now destruct (Nat.nlt_0_r (S m)).
      simpl.
      rewrite map_length.
      now apply PeanoNat.lt_S_n.
    * case_eq (S m =? length inp)%nat; intros H.
      -- apply Nat.eqb_eq in H.
         rewrite <- H.
         assert (H0 := Nat.lt_succ_diag_r m).
         apply Nat.ltb_lt in H0.
         rewrite H0.
         rewrite H at 1.
         rewrite <- (map_length  (fun f : nat -> bool => f (length (ListNeuro nc)))) at 1.
         rewrite afternlist_nil.
         simpl.
         now rewrite repeat_cons_same.
      -- assert (m <? length inp = false)%nat as H0.
         apply Nat.ltb_ge in Hm.
         apply Nat.ltb_ge.
         apply Nat.le_lteq in Hm as [Hm|Hm].
         now apply PeanoNat.lt_n_Sm_le.
         rewrite Hm in H.
         rewrite Nat.eqb_refl in H.
         inversion H.
         rewrite H0.
         simpl.
         now rewrite repeat_cons_same.
Qed.

Theorem Series_Delayer_Effect: forall n n0 inp nc,
    is_initial nc ->
    Series nc ->
    In n0 (ListNeuro nc) ->
    Id (Feature n0) = 0%nat ->
    Tau (Feature n0) <= Weights (Feature n0) (length (ListNeuro nc)) ->
    (forall m id, In m (ListNeuro nc) ->
                  Id (Feature m) = S id ->
                  Tau (Feature m) <= Weights (Feature m) id) ->
    (n < (length (ListNeuro nc)))%nat ->
    output_neuron nc inp n =
      if (n <? length inp + 1)%nat 
      then afternlist _ n%nat (map (fun f => f (length (ListNeuro nc))) inp) ++ List.repeat false (S n)
      else List.repeat false (S (length inp)).
Proof.
  intros [|n] n0 inp nc Hinit Hserie Hin0 Hid0 Htau0 Htau Hlen.
  - simpl.
    assert (0 <? length inp + 1 = true)%nat as H.
    apply Nat.ltb_lt.
    rewrite Nat.add_1_r.
    apply Nat.lt_0_succ.
    rewrite H.
    now apply (Series_Output_n_Input_0 n0).
  - rewrite Nat.add_1_r.
    assert (S n <? S (length inp) = (n <? length inp))%nat.
    case_eq (n <? length inp)%nat; intros H.
    apply Nat.ltb_lt.
    apply Nat.succ_lt_mono.
    now apply Nat.ltb_lt.
    apply Nat.ltb_ge.
    apply Peano.le_n_S.
    now apply Nat.ltb_ge.
    rewrite H.
    now apply (Series_Output_n_Input_succ_delayer _ n0).
Qed.


(* Parallel Composition *)


Theorem ParalComp_Delayer_Effect_0: forall n inp nc,
    is_initial nc ->
    ParallelComposition nc ->
    In n (ListNeuro nc) ->
    Id (Feature n) = 0%nat ->
    Tau (Feature n) <= Weights (Feature n) (length (ListNeuro nc)) ->
    output_neuron nc inp 0 =
      map (fun f => f (length (ListNeuro nc))) inp ++ [false].
Proof.
  intros n inp nc Hinit Hpc Hin Hid Htau.
  rewrite <- Hid.
  assert (Hoi := ParalComp_One_Input_Or_Less_0 _ _ Hpc Hin Hid).
  apply One_Input_NC_delay_Ext; trivial.
  rewrite (OneSupplementPC _ Hpc).
  rewrite Nat.add_1_r.
  apply Nat.lt_succ_diag_r.
Qed.


Lemma ParalComp_Output_n_Input_succ: forall n id inp nc,
    is_initial nc ->
    ParallelComposition nc ->
    In n (ListNeuro nc) ->
    Id (Feature n) = S id ->
    Tau (Feature n) <= Weights (Feature n) 0 ->
    output_neuron nc inp (Id (Feature n)) =
      tl (output_neuron nc inp 0) ++ [false].
Proof.
  intros n1 id inp nc Hinit Hpc Hin1 Hid1 Htau.
  apply IdInfLen in Hin1 as H.
  rewrite Hid1 in H.
  apply (Nat.lt_trans _ _ _ (Nat.lt_0_succ _))in H.
  apply len_inf_in_listneuro in H as [n2 [Hin2 Hid2]].
  rewrite <- Hid2.
  apply One_Input_NC_delay_Int; trivial; rewrite Hid2; trivial.
  now apply (ParalComp_One_Input_Or_Less_succ _ id).
Qed.


Theorem ParalComp_Delayer_Effect_Succ: forall n n0 m inp nc,
    is_initial nc ->
    ParallelComposition nc ->
    In n0 (ListNeuro nc) ->
    Id (Feature n0) = 0%nat ->
    Tau (Feature n0) <= Weights (Feature n0) (length (ListNeuro nc)) ->
    In m (ListNeuro nc) ->
    Id (Feature m) = S n ->
    Tau (Feature m) <= Weights (Feature m) 0 ->
    (S n < (length (ListNeuro nc)))%nat ->
    output_neuron nc inp (S n) =
      if (0 <? length inp)%nat 
      then tl (map (fun f => f (length (ListNeuro nc))) inp) ++ [false; false] 
      else [false].
Proof.
  intros n n0 m inp nc Hinit Hpc Hin0 Hid0 Htau0 Hin Hid Htau Hlen.
  rewrite <- Hid.
  rewrite (ParalComp_Output_n_Input_succ _ n); trivial.
  rewrite (ParalComp_Delayer_Effect_0 n0); trivial.
  destruct inp as [|i1 [|i2 tl]]; simpl; trivial.
  now rewrite <- app_assoc.
Qed.

(*****************************************)

(** Properties : comparing between potential and tau **)


Lemma potential_ti_sup_tau : forall nf inp1 inp2 id1 id2 n1 len,
    Tau nf <= Weights nf id1 ->
    Tau nf <= Weights nf id2 ->
    (id1 < n1)%nat -> 
    (n1 <= id2)%nat -> 
    Two_Inputs_Or_Less nf id1 id2 len ->
    Tau nf <=? potential (Weights nf)
                         (fun x : nat =>
                            if (x <? n1)%nat then inp1 x else inp2 x)
                         len = inp1 id1 || inp2 id2.
Proof.
  intros nf inp1 inp2 id1 id2 n1 len Htau1 Htau2 Hid1 Hid2 Hti.
  rewrite (Qeq_bool_equiv_r _ _ _ (potential_ti _ _ _ _ _ Hti)).
  apply Nat.ltb_lt in Hid1.
  apply Nat.ltb_ge in Hid2.
  rewrite Hid1, Hid2.
  case_eq (inp1 id1); intros H.
  - apply Qleb_plus_pos_r; apply Qle_bool_iff; trivial.
    * destruct (inp2 id2).
      revert Htau2.
      apply Qle_trans.
      apply Qlt_le_weak.
      apply nf.
      apply Qle_refl.
  - simpl.
    rewrite (Qeq_bool_equiv_r _ _ _ (Qplus_0_l _)).
    * destruct (inp2 id2).
      now apply Qle_bool_iff.
      apply Qleb_lt.
      apply nf.
Qed.



Lemma potential_ti_sup_tau2 : forall nf inp1 inp2 id1 id2 n1 len,
    Weights nf id1 < 0 ->
    (id1 < n1)%nat ->
    (n1 <= id2)%nat ->
    Tau nf <= Weights nf id2 ->
    Two_Inputs_Or_Less nf id1 id2 len ->
    Tau nf <=?
      potential (Weights nf)
                (fun x : nat =>
                   if (x <? n1)%nat then inp1 x else inp2 x) len =
      inp2 id2 && ((negb (inp1 id1)) || (Tau nf <=? Weights nf id1 + Weights nf id2)).
Proof.
  intros nf inp1 inp2 id1 id2 n1 len Htau1 Hid1 Hid2 Htau2 Hti.
  rewrite (Qeq_bool_equiv_r _ _ _ (potential_ti _ _ _ _ _ Hti)).
  apply Nat.ltb_lt in Hid1.
  rewrite Hid1.
  apply Nat.ltb_ge in Hid2.
  rewrite Hid2.
  destruct (inp2 id2).
  - destruct (inp1 id1); trivial.
    rewrite (Qeq_bool_equiv_r _ _ _ (Qplus_0_l _)).
    now apply Qle_bool_iff.
  - rewrite (Qeq_bool_equiv_r _ _ _ (Qplus_0_r _)).
    simpl.
    destruct (inp1 id1)%nat; apply Qleb_lt; [apply (Qlt_trans _ _ _ Htau1)|]; apply nf.
Qed.



Lemma potential_sup_tau_or_0 : forall n m inp,
    (forall id, (id < m)%nat ->
                Tau (Feature n) <= Weights (Feature n) id \/
                  Weights (Feature n) id == 0) ->
    Tau (Feature n) <=
      potential (Weights (Feature n)) inp m \/
      potential (Weights (Feature n)) inp m == 0.
Proof.
  intros n m inp Hw.
  induction m as [|m' IH].
  - right; apply Qeq_refl.
  - simpl.
    destruct IH as [IH|IH].
    intros id H.
    apply Hw.
    now apply Nat.lt_lt_succ_r.
    * destruct (inp m').
      -- left.
         apply Qle_plus_pos_r; trivial.
         destruct (Hw m') as [Hw1|Hw1].
         apply Nat.lt_succ_diag_r.
         ** revert Hw1.
            apply Qle_trans.
            apply Qlt_le_weak.
            apply (Feature n).
         ** apply Qle_lteq.
            right.
            now apply Qeq_sym.
      -- now left.
    * destruct (inp m').
      -- destruct (Hw m') as [Hw1|Hw1].
         apply Nat.lt_succ_diag_r.
         left.
         apply Qle_plus_pos_l; trivial.
         ** apply Qle_lteq.
            right.
            now apply Qeq_sym.
         ** right.
            rewrite <- plusQ_0.
            now apply Qeq_plus_compat.
      -- now right.
Qed.


Lemma potential_sup_tau_CI : forall nc n inp1 inp2,
    ContraInhib nc ->
    In n (ListNeuro nc) ->
    Id (Feature n) = 0%nat ->
    inp2 2%nat = true ->
    Tau (Feature n) <= Weights (Feature n) 1 + Weights (Feature n) 2 ->
    Tau (Feature n) <=
      potential (Weights (Feature n)) (fun x : nat =>
                            if (x <? 2)%nat then inp1 x else inp2 x) 4.
Proof.
  intros nc n inp1 inp2 Hci Hin Hid Hinp2 Hw.
  apply Qle_bool_iff.
  rewrite (potential_ti_sup_tau2 _ _ _ 1 2); trivial.
  rewrite Hinp2.
  destruct (negb (inp1 1%nat)); trivial.
  simpl.
  now apply Qle_bool_iff.
  apply Hci; trivial.
  apply Nat.lt_1_2.
  apply (Qle_trans _ _ _ Hw).
  apply Qle_inf_0_trans_l; [apply Qlt_le_weak; now apply Hci|apply Qle_refl].
  assert (1 < length (ListNeuro nc))%nat.
  rewrite ListNeuroLengthCI; trivial.
  apply Nat.lt_1_2.
  apply len_inf_in_listneuro in H as [n2 [H H0]].
  rewrite <- H0 at 1.
  apply (Two_Inputs_Two_Neurons3 _ _ _ Hin Hid H0).
  now apply Hci.
Qed.


Lemma potential_sup_tau_or_0_NL : forall n inp,
    inp 2%nat = true ->
    Weights (Feature n) 0 == 0 ->
    Weights (Feature n) 1 == - Weights (Feature n) 2 ->
    Tau (Feature n) <= Weights (Feature n) 2 ->
    Tau (Feature n) <= potential (Weights (Feature n)) inp 3 \/
      potential (Weights (Feature n)) inp 3 == 0.
Proof.
  intros n inp Hinp Hw1 Hw2 Hw3.
  assert (Weights (Feature n) 1 + Weights (Feature n) 2 == 0).
  - apply (Qplus_inj_r _ _ (Weights (Feature n) 2)) in Hw2.
    apply (Qeq_trans _ _ _ Hw2).
    apply (Qeq_trans _ _ _ (Qplus_comm _ _)).
    apply (Ropp_def Qsrt).
  - simpl.
    rewrite Hinp.
    destruct (inp 1%nat); destruct (inp 0%nat).
    * right.
      rewrite <- plusQ_0 at 2.
      rewrite <- ! Qplus_assoc.
      apply Qplus_inj_l.
      rewrite <- plusQ_0.
      now apply Qeq_plus_compat.
    * right.
      rewrite <- plusQ_0 at 2.
      rewrite <- ! Qplus_assoc.
      now apply Qplus_inj_l.
    * left.
      apply Qle_plus_pos_l; trivial.
      apply Qle_plus_pos_l.
      apply Qle_lteq.
      right. now apply Qeq_sym.
      apply Qle_refl.
    * left.
      apply Qle_plus_pos_l; trivial.
      apply Qle_refl.
Qed.

Lemma potential_sup_tau_or_0_input_false : forall n m id1 id2 inp,
    inp id1 = false ->
    inp id2 = true ->
    Two_Inputs_Or_Less (Feature n) id1 id2 m ->
    Tau (Feature n) <= Weights (Feature n) id2 ->
    Tau (Feature n) <= potential (Weights (Feature n)) inp m.
Proof.
  intros n m id1 id2 inp Hinp1 Hinp2 Hti Hw1.
  apply (fun H => Qle_eq_r _ _ _ H (Qeq_sym _ _ (potential_ti _ _ _ _ _ Hti))).
  rewrite Hinp1, Hinp2.
  apply Qle_plus_pos_l; trivial.
  apply Qle_refl.
Qed.


Lemma potential_inf_tau_or_eq: forall n m id1 id2 inp,
    inp id1 = true ->
    inp id2 = true ->
    Two_Inputs_Or_Less (Feature n) id1 id2 m ->
    Weights (Feature n) id1 + Weights (Feature n) id2 < Tau (Feature n) ->
    potential (Weights (Feature n)) inp m < Tau (Feature n) /\
      potential (Weights (Feature n)) inp m == Weights (Feature n) id1 + Weights (Feature n) id2.
Proof.
  intros n m id1 id2 inp Hinp1 Hinp2 Hti Hw2.
  split.
  - apply (fun H => Qlt_eq_l _ _ _ H (Qeq_sym _ _ (potential_ti _ _ _ _ _ Hti))).
    now rewrite Hinp1, Hinp2.
  - apply (Qeq_trans _ _ _ (potential_ti _ _ _ _ _ Hti)).
    rewrite Hinp1, Hinp2.
    apply Qeq_refl.
Qed.


(** Properties on curpot_neuron **)


Lemma curpot_sup_tau_or_eq_0 : forall n i inp nc,
    is_initial nc ->
    In n (ListNeuro nc) ->
    (forall i l1 l2,
        inp = l1 ++ i :: l2 ->
        Tau (Feature n) <= potential (Weights (Feature n)) (fun x : nat =>
     if (x <? length (ListNeuro nc))%nat
     then List.hd false (output_neuron nc l2 x)
     else i x) (length (ListNeuro nc) + SupplInput nc) \/
      potential (Weights (Feature n)) (fun x : nat =>
     if (x <? length (ListNeuro nc))%nat
     then List.hd false (output_neuron nc l2 x)
     else i x) (length (ListNeuro nc) + SupplInput nc) == 0) ->
    curpot_neuron nc (i :: inp) (Id (Feature n)) ==
      potential (Weights (Feature n)) (fun x : nat =>
     if (x <? length (ListNeuro nc))%nat
     then hd false (output_neuron nc inp x)
     else i x) (length (ListNeuro nc) + SupplInput nc).
Proof.
  intros n i inp nc Hinit Hin Htau.
  rewrite NstepsCircuit_curpot_neuron; trivial.
  apply (fun H => Qeq_trans _ _ _ H (Qplus_0_r _)).
  apply Qplus_inj_l.
  assert (Tau (Feature n) <= curpot_neuron nc inp (Id (Feature n)) \/ curpot_neuron nc inp (Id (Feature n)) == 0) as [H|H].
  - induction inp as [|hd tl IH].
    * unfold curpot_neuron.
      simpl.
      rewrite (find_neuro_in _ _ Hin).
      right.
      now apply (is_initial_curpot _ Hinit).
    * rewrite NstepsCircuit_curpot_neuron; trivial.
      destruct IH as [IH|IH].
      intros i' l1 l2 H.
      subst.
      now apply (Htau i' (hd :: l1) l2).
      -- apply Qle_bool_iff in IH.
         rewrite IH.
         destruct (Htau hd [] tl) as [Htau1|Htau1]; trivial.
         left.
         now apply (fun H => Qle_eq_r _ _ _ H (Qeq_sym _ _ (Qplus_0_r _))).
         right.
         now apply (Qeq_trans _ _ _ (Qplus_0_r _)).
      -- rewrite (Qeq_bool_equiv_r _ _ _ IH).
         rewrite (proj2 (Qleb_lt _ _) (PosTau _)).
         destruct (Htau hd [] tl) as [Htau1|Htau1]; trivial.
         left.
         apply Qle_plus_pos_r; trivial.
         apply Qmult_le_0_compat.
         apply (Feature n).
         apply Qle_lteq.
         now right.
         right.
         rewrite <- plusQ_0.
         apply Qeq_plus_compat; trivial.
         apply mul_0_iff.
         right.
         now apply Qeq_sym in IH.         
  - apply Qle_bool_iff in H.
    rewrite H.
    apply Qeq_refl.
  - rewrite (Qeq_bool_equiv_r _ _ _ H).
    rewrite (proj2 (Qleb_lt _ _) (PosTau _)).
    apply mul_0_iff.
    now right.
Qed.


Lemma if_curpot_sup_tau_eq_0_NL : forall n inp nc,
    is_initial nc ->
    NegativeLoop nc ->
    In n (ListNeuro nc) ->
    Id (Feature n) = 0%nat ->
    (forall i, In i inp -> i 2%nat = true) ->
    Tau (Feature n) <= Weights (Feature n) 2 ->
    Weights (Feature n) 1 == - Weights (Feature n) 2 ->
    (if Tau (Feature n) <=? curpot_neuron nc inp (Id (Feature n))
     then 0
     else Leak_Factor (Feature n) * curpot_neuron nc inp (Id (Feature n))) == 0.
Proof.
  intros n inp nc Hinit Hneg Hin Hid Hinp Htau2 Htau3.
  assert (Htau1 := WId (Feature n)).
  rewrite Hid in Htau1.
  assert (Tau (Feature n) <= curpot_neuron nc inp (Id (Feature n)) \/ curpot_neuron nc inp (Id (Feature n)) == 0) as [H|H].
  induction inp as [|hd tl IH].
  - unfold curpot_neuron.
    simpl.
    rewrite (find_neuro_in _ _ Hin).
    right.
    now apply (is_initial_curpot _ Hinit).
  - rewrite NstepsCircuit_curpot_neuron; trivial.
    rewrite OneSupplementNL, ListNeuroLengthNL; trivial.
    destruct IH as [IH|IH].
    intros i H.
    apply Hinp.
    now right.
    * apply Qle_bool_iff in IH.
      rewrite IH.
      destruct (potential_sup_tau_or_0_NL n (fun x : nat =>
     if (x <? 2)%nat then List.hd false (output_neuron nc tl x) else hd x)) as [H|H]; trivial.
      rewrite Nat.ltb_irrefl.
      apply Hinp.
      now left.
      now rewrite Htau1.
      left.
      now apply (fun H => Qle_eq_r _ _ _ H (Qeq_sym _ _ (Qplus_0_r _))).
      right.
      now apply (Qeq_trans _ _ _ (Qplus_0_r _)).
    * rewrite (Qeq_bool_equiv_r _ _ _ IH).
      rewrite (proj2 (Qleb_lt _ _) (PosTau _)).
      destruct (fun H H0 => potential_sup_tau_or_0_NL _ (fun x : nat =>
                                                      if x <? 2
                                                      then List.hd false (output_neuron nc tl x)
                                                      else hd x)%nat H H0 Htau3 Htau2) as [H0|H0].
      rewrite Nat.ltb_irrefl.
      apply Hinp.
      now left.
      now rewrite Htau1.
      left.
      apply Qle_plus_pos_r; trivial.
      apply Qmult_le_0_compat.
      apply (Feature n).
      apply Qle_lteq.
      now right.
      right.
      rewrite <- plusQ_0.
      apply Qeq_plus_compat; trivial.
      apply mul_0_iff.
      right.
      now apply Qeq_sym in IH.
  - apply Qle_bool_iff in H.
    rewrite H.
    apply Qeq_refl.
  - rewrite (Qeq_bool_equiv_r _ _ _ H).
    rewrite (proj2 (Qleb_lt _ _) (PosTau _)).
    apply mul_0_iff.
    now right.
Qed.


(* Properties : comparison of curpot_neuron and tau for the archetype PL, NL and CI *)

Lemma curpot_sup_tauPL : forall n n2 i inp nc,
    is_initial nc ->
    PositiveLoop nc ->
    In n (ListNeuro nc) ->
    In n2 (ListNeuro nc) ->
    Id (Feature n) = 0%nat ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n) <= Weights (Feature n) 1 ->
    Tau (Feature n) <= Weights (Feature n) 2 ->
    Tau (Feature n) <=? curpot_neuron nc (i :: inp) 0 = i 2%nat || (hd false (output_neuron nc inp 1)).
Proof.
  intros n1 n2 i inp nc Hinit HPos Hin Hin2 Hid1 Hid2 Htau1 Htau2.
  rewrite <- Hid1 at 1.
  rewrite (fun H => Qeq_bool_equiv_r _ _ _ (curpot_sup_tau_or_eq_0 _ _ _ _ Hinit Hin H)).
  rewrite (potential_ti_sup_tau (Feature n1) (fun x => hd false (output_neuron nc inp x)) _ 1 2 _); trivial; try solve [rewrite OneSupplementPL, ListNeuroLengthPL; trivial; now apply Two_Inputs_Two_Neurons|rewrite ListNeuroLengthPL; trivial; try solve [apply Nat.lt_1_2]].
  now rewrite orb_comm.
  intros i0 l1 l2 H.
  assert (forall id : nat,
      (id < length (ListNeuro nc) + SupplInput nc)%nat ->
      Tau (Feature n1) <= Weights (Feature n1) id \/ Weights (Feature n1) id == 0).
  intros id Hid.
  rewrite ListNeuroLengthPL, OneSupplementPL in Hid; trivial.
  apply PeanoNat.lt_n_Sm_le in Hid.
  destruct id as [|[|[|m]]].
  right.
  rewrite <- Hid1.
  rewrite WId.
  apply Qeq_refl.
  now left.
  now left.
  do 2 apply PeanoNat.lt_S_n in Hid.
  now destruct (Nat.nlt_0_r m).
  now apply potential_sup_tau_or_0.
Qed.



Lemma curpot_sup_tauNL : forall n i (inp : list (nat -> bool)) nc,
    is_initial nc ->
    NegativeLoop nc ->
    In n (ListNeuro nc) ->
    Id (Feature n) = 0%nat ->
    i 2%nat = true ->
    Tau (Feature n) <= Weights (Feature n) 2 ->
    hd false (output_neuron nc inp 1) = false ->
    0 <= curpot_neuron nc inp 0 ->
    Tau (Feature n) <= curpot_neuron nc (i :: inp) 0.
Proof.
  intros n i inp nc Hinit Hneg Hin Hid Hi Hw1 Hlast Htau.
  rewrite <- Hid.
  rewrite NstepsCircuit_curpot_neuron; trivial.
  apply Qle_plus_pos_r.
  apply (potential_sup_tau_or_0_input_false _ _ 1 2); trivial; try solve [now rewrite ListNeuroLengthNL].
  rewrite ListNeuroLengthNL, OneSupplementNL; trivial.
  now apply Two_Inputs_Two_Neurons.
  case_eq (Tau (Feature n) <=? curpot_neuron nc inp (Id (Feature n))); intros H.
  apply Qle_refl.
  apply Qmult_le_0_compat.
  apply (Feature n).
  now rewrite Hid.
Qed.


Lemma curpot_sup_tauNL_2 : forall n i inp nc,
    is_initial nc ->
    NegativeLoop nc ->
    In n (ListNeuro nc) ->
    i 2%nat = true ->
    Id (Feature n) = 0%nat ->
    0 <= Weights (Feature n) 1 + Weights (Feature n) 2 ->
    (1 + Leak_Factor (Feature n)) * (Weights (Feature n) 1 + Weights (Feature n) 2) < Tau (Feature n) ->
    hd false (output_neuron nc inp 1) = true ->
    Tau (Feature n) <= curpot_neuron nc inp 0 ->
    curpot_neuron nc (i :: inp) 0 == Weights (Feature n) 1 + Weights (Feature n) 2.
Proof.
  intros n i inp nc Hinit Hneg Hin Hi Hid Hw2 Hw3 Hlast Htau.
  rewrite <- Hid at 1.
  rewrite (NstepsCircuit_curpot_neuron _ _ _ _ Hin); trivial.
  simpl.
  apply Qle_bool_iff in Htau.
  rewrite <- Hid in Htau.
  rewrite Htau.
  assert (H0 := proj1 (LeakRange (Feature n))).
  apply Qmul_more_1_le in Hw3; trivial.
  destruct (potential_inf_tau_or_eq n (length (ListNeuro nc) + SupplInput nc) 1 2 (fun x : nat =>
     if (x <? length (ListNeuro nc))%nat
     then hd false (output_neuron nc inp x)
     else i x)) as [H H0']; trivial; try solve [now rewrite ListNeuroLengthNL].
  rewrite ListNeuroLengthNL, OneSupplementNL; trivial.
  now apply Two_Inputs_Two_Neurons.
  now apply (Qeq_trans _ _ _ (Qplus_0_r _)).
Qed.



Lemma curpot_sup_tauNL_3 : forall n i inp nc,
    is_initial nc ->
    NegativeLoop nc ->
    In n (ListNeuro nc) ->
    i 2%nat = true ->
    Id (Feature n) = 0%nat ->
    0 <= Weights (Feature n) 1 + Weights (Feature n) 2 ->
    (1 + Leak_Factor (Feature n)) * (Weights (Feature n) 1 + Weights (Feature n) 2) < Tau (Feature n) ->
    hd false (output_neuron nc inp 1) = true ->
    curpot_neuron nc inp 0 == Weights (Feature n) 1 + Weights (Feature n) 2 ->
    curpot_neuron nc (i :: inp) 0 == (1%Q + Leak_Factor (Feature n)) * (Weights (Feature n) 1 + Weights (Feature n) 2).
Proof.
  intros n i inp nc Hinit Hneg Hin Hi Hid Hw2 Hw3 Hlast Htau.
  rewrite <- Hid at 1.
  rewrite (NstepsCircuit_curpot_neuron _ _ _ _ Hin); trivial.
  assert (H0 := proj1 (LeakRange (Feature n))).
  apply Qmul_more_1_le in Hw3 as Hw1; trivial.
  apply (fun H => Qlt_eq_l _ _ _ H (Qeq_sym _ _ Htau)) in Hw1 as Htau2.
  apply Qleb_lt in Htau2.
  rewrite Hid, Htau2.
  apply (Qeq_trans _ ((Weights (Feature n) 1 + Weights (Feature n) 2) + Leak_Factor (Feature n) * (Weights (Feature n) 1 + Weights (Feature n) 2))).
  - apply Qeq_plus_compat; trivial.
    apply (potential_inf_tau_or_eq n (length (ListNeuro nc) + SupplInput nc) 1 2 (fun x : nat =>
     if (x <? length (ListNeuro nc))%nat
     then hd false (output_neuron nc inp x)
     else i x)); trivial; try solve [now rewrite ListNeuroLengthNL].
    rewrite ListNeuroLengthNL, OneSupplementNL; trivial.
    now apply Two_Inputs_Two_Neurons.
    now apply Qeq_mul_compat_r.
  - apply Qeq_sym.
    apply (Qeq_trans _ _ _ (Qmult_plus_distr_l _ _ _)).
    apply Qplus_inj_r.
    apply Qmult_1_l.
Qed.



Lemma curpot_sup_tauCI : forall n n2 i inp nc,
    is_initial nc ->
    ContraInhib nc ->
    In n (ListNeuro nc) ->
    Id (Feature n) = 0%nat ->
    Id (Feature n2) = 1%nat ->
    (forall i0 : nat -> bool, In i0 (i :: inp) -> i0 2%nat = true) ->
    Tau (Feature n) <= Weights (Feature n) 1 + Weights (Feature n) 2 ->
    Tau (Feature n) <= curpot_neuron nc (i :: inp) 0.
Proof.
  intros n n2 i inp nc Hinit Hci Hin Hid1 Hid2 Hi Htau1.
  apply Qle_bool_iff.
  rewrite <- Hid1.
  rewrite (fun H => Qeq_bool_equiv_r _ _ _ (curpot_sup_tau_or_eq_0 _ _ _ _ Hinit Hin H)).
  rewrite (potential_ti_sup_tau2 (Feature n) (fun x => hd false (output_neuron nc _ x)) _ 1 2 _); trivial; try solve [rewrite ListNeuroLengthCI; trivial; try solve [apply Nat.lt_1_2]].
  rewrite Hi.
  apply Qle_bool_iff in Htau1.
  rewrite Htau1.
  now rewrite orb_true_r.
  now left.
  now apply Hci.
  apply (Qle_trans _ _ _ Htau1); apply Qle_inf_0_trans_l; [apply Qlt_le_weak; now apply Hci|apply Qle_refl].
  rewrite OneSupplementCI, ListNeuroLengthCI; trivial.
  rewrite <- Hid2 at 1.
  apply (Two_Inputs_Two_Neurons3 _ _ nc); trivial.
  now apply Hci.
  intros i0 l1 l2 H.
  left.
  rewrite ListNeuroLengthCI, OneSupplementCI; trivial.
  apply (potential_sup_tau_CI _ _ _ _ Hci); trivial.
  apply Hi.
  subst.
  right.
  apply in_or_app.
  right; now left.
Qed.



Lemma curpot_sup_tauCI_2 : forall n n2 i inp nc,
    is_initial nc ->
    ContraInhib nc ->
    In n (ListNeuro nc) ->
    Id (Feature n) = 1%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 0%nat ->
    i 3%nat = true ->
    Weights (Feature n) 0 + Weights (Feature n) 3 <= 0 ->
    hd false (output_neuron nc inp 0) = true ->
    curpot_neuron nc (i :: inp) 1 < Tau (Feature n).
Proof.
  intros n n2 i inp nc Hinit Hci Hin Hid Hin2 Hid2 Hi Hw3 Hlast.
  rewrite <- Hid.
  rewrite (NstepsCircuit_curpot_neuron _ _ _ _ Hin); trivial.
  assert (Two_Inputs_Or_Less (Feature n) (Id (Feature n2)) 3
    (length (ListNeuro nc) + SupplInput nc)) as Hti.
  rewrite OneSupplementCI, ListNeuroLengthCI; trivial.
  apply (Two_Inputs_Two_Neurons4 _ _ nc); trivial.
  now apply Hci.
  case_eq (Tau (Feature n) <=? curpot_neuron nc inp (Id (Feature n))); intros Htau.
  - apply (fun H => Qlt_eq_l _ _ _ H (Qeq_sym _ _ (Qplus_0_r _))).
    apply (potential_inf_tau_or_eq _ _ 0 3); trivial; try solve [now rewrite ListNeuroLengthCI].
    now rewrite <- Hid2 at 1.
    apply (Qle_lt_trans _ 0); trivial.
    apply PosTau.
  - apply Qlt_inf_0_trans_l.
    apply (fun H => Qle_eq_l _ _ _ H (Qeq_sym _ _ (potential_ti _ _ _ _ _ Hti))).
    rewrite Hid2.
    rewrite ListNeuroLengthCI; trivial.
    simpl.
    now rewrite Hlast, Hi.
    apply Qleb_lt in Htau.
    apply Qmul_0_1_lt; trivial.
    apply Feature.
    apply Feature.
Qed.





(*** Positive Loop ***)


(* External input : always false *)

Theorem PL_Amplifier_input_false : forall inp n1 n2 nc,
    is_initial nc ->
    PositiveLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) 1 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i, In i inp -> i 2%nat = false) ->
    output_neuron nc inp 0 = List.repeat false (length inp + 1) /\
      output_neuron nc inp 1 = List.repeat false (length inp + 1).
Proof.
  intros inp n1 n2 nc Hinit HPos Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp.
  rewrite <- Hid1 at 1.
  rewrite <- Hid2 at 2.
  induction inp as [|i inp IH].
  - split; simpl; rewrite output_neuron_Output; trivial.
    apply (is_initial_output _ Hinit _ Hin1).
    apply (is_initial_output _ Hinit _ Hin2).
  - destruct IH as [IH1 IH2]; [intros i0 Hin; apply Hinp; now right|].
    assert (output_neuron nc (i :: inp) (Id (Feature n1)) = repeat false (length (i :: inp) + 1)) as H.
    * rewrite (proj1 (curpot_neuron_output_false _ _ _ _ Hin1)), IH1; trivial.
      apply Qleb_lt.
      rewrite Hid1.
      rewrite (curpot_sup_tauPL _ n2); trivial.
      rewrite <- Hid2 at 2.
      rewrite IH2.
      rewrite Hinp, Nat.add_1_r; trivial.
      now left.
    * split; trivial.
      rewrite <- Hid1 in Htau3.
      rewrite (One_Input_NC_delay_Int _ _ _ _ Hinit Hin2 Hin1 (One_Input_Or_Less_PL_1 _ _ _ Hid1 Hin2 Hid2 HPos)); trivial.
      rewrite H.
      simpl.
      now rewrite repeat_cons_same.
Qed.


(* External input : last input true and the other false *)

Lemma PL_Output_Amplifier_1_true_aux : forall i inp n1 n2 nc,
    is_initial nc ->
    PositiveLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) 1 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i, In i inp -> i 2%nat = false) ->
    i 2%nat = true ->
    output_neuron nc (i :: inp) 0 = true :: List.repeat false (length inp + 1) /\ output_neuron nc (i :: inp) 1 = List.repeat false (length inp + 2).
Proof.
  intros i inp n1 n2 nc Hinit HPos Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp Hi.
  assert (output_neuron nc (i :: inp) 0 = true :: repeat false (length inp + 1)) as H.
  - rewrite <- Hid1 at 1.
    rewrite (proj1 (curpot_neuron_output_true _ _ _ _ Hin1)); [f_equal; rewrite Hid1; apply (PL_Amplifier_input_false _ _ _ _  Hinit HPos Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp)|].
    apply Qle_bool_iff.
    rewrite Hid1.
    rewrite (curpot_sup_tauPL _ n2); trivial.
    now rewrite Hi.
  - split; trivial.
    rewrite <- Hid2 at 1.
    rewrite <- Hid1 in Htau3.
    rewrite (One_Input_NC_delay_Int _ _ _ _ Hinit Hin2 Hin1 (One_Input_Or_Less_PL_1 _ _ _ Hid1 Hin2 Hid2 HPos)); trivial.
    rewrite Hid1, H.
    simpl.
    rewrite <- repeat_cons_same.
    rewrite ZL0, Nat.add_assoc.
    now rewrite ! Nat.add_1_r.
Qed.


(** External input : two sequential true after always false **)

Lemma PL_Output_Amplifier_2_true_aux : forall i1 i2 inp n1 n2 nc,
    is_initial nc ->
    PositiveLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) 1 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i, In i inp -> i 2%nat = false) ->
    i1 2%nat = true ->
    i2 2%nat = true ->
    output_neuron nc (i1 :: i2 :: inp) 0 = true :: true :: List.repeat false (length inp + 1) /\
      output_neuron nc (i1 :: i2 :: inp) 1 = true :: List.repeat false (length inp + 2).
Proof.
  intros i1 i2 inp n1 n2 nc Hinit HPos Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp Hi1 Hi2.
  assert (output_neuron nc (i1 :: i2 :: inp) 0 = true :: true :: repeat false (length inp + 1)) as H.
  - rewrite <- Hid1 at 1.
    rewrite (proj1 (curpot_neuron_output_true _ _ _ _ Hin1)); [f_equal; rewrite Hid1; apply (PL_Output_Amplifier_1_true_aux _ _ _ _ _  Hinit HPos Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp Hi2)|]. 
    apply Qle_bool_iff.
    rewrite Hid1.
    rewrite (curpot_sup_tauPL _ n2); trivial.
    now rewrite Hi1.
  - split; trivial.
    rewrite <- Hid2 at 1.
    rewrite <- Hid1 in Htau3.
    rewrite (One_Input_NC_delay_Int _ _ _ _ Hinit Hin2 Hin1 (One_Input_Or_Less_PL_1 _ _ _ Hid1 Hin2 Hid2 HPos)); trivial.
    rewrite Hid1, H.
     simpl.
    rewrite <- repeat_cons_same.
    rewrite ZL0, Nat.add_assoc.
    now rewrite ! Nat.add_1_r.
Qed.


Theorem PL_Output_Amplifier_input_2_true : forall i1 i2 inp1 inp2 n1 n2 nc,
    is_initial nc ->
    PositiveLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) 1 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i, In i inp2 -> i 2%nat = false) ->
    i1 2%nat = true ->
    i2 2%nat = true ->
    output_neuron nc (inp1 ++ i1 :: i2 :: inp2) 0 = List.repeat true (length inp1 + 2) ++ List.repeat false (length inp2 + 1) /\
      output_neuron nc (inp1 ++ i1 :: i2 :: inp2) 1 =  List.repeat true (length inp1 + 1) ++ List.repeat false (length inp2 + 2).
Proof.
  intros i1 i2 inp1 inp2 n1 n2 nc Hinit HPos Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp2 Hi1 Hi2.
  rewrite <- Hid1 at 1.
  rewrite <- Hid2 at 3.
  induction inp1 as [|i inp1 IH].
  - simpl.
    rewrite Hid1, Hid2.
    apply (PL_Output_Amplifier_2_true_aux _ _ _ n1 n2); trivial.
  - destruct IH as [IH1 IH2].
    assert (output_neuron nc ((i :: inp1) ++ i1 :: i2 :: inp2) (Id (Feature n1)) =
  repeat true (length (i :: inp1) + 2) ++ repeat false (length inp2 + 1)) as H.
    * simpl.
      rewrite (proj1 (curpot_neuron_output_true _ _ _ _ Hin1)); [now f_equal|].
      apply Qle_bool_iff.
      rewrite Hid1.
      rewrite (curpot_sup_tauPL _ n2); trivial.
      rewrite <- Hid2 at 2.
      rewrite IH2, Nat.add_1_r.
      apply orb_true_r.
    * split; trivial.
      rewrite <- Hid1 in Htau3.
      rewrite (One_Input_NC_delay_Int _ _ _ _ Hinit Hin2 Hin1 (One_Input_Or_Less_PL_1 _ _ _ Hid1 Hin2 Hid2 HPos)); trivial.
      rewrite H.
      rewrite ! ZL0, ! Nat.add_assoc.
      rewrite ! Nat.add_1_r.
      simpl.
      rewrite <- ! app_assoc, <- app_comm_cons.
      do 4 f_equal.
      now rewrite repeat_cons_same.
Qed.


(** External input : one true and other are always false **)

Theorem PL_Oscillation_1_true : forall i inp1 inp2 n1 n2 nc,
    is_initial nc ->
    PositiveLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) 1 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i, In i inp1 -> i 2%nat = false) ->
    (forall i, In i inp2 -> i 2%nat = false) ->
    i 2%nat = true ->
    output_neuron nc (inp1 ++ i :: inp2) 0 = repeat_seq _ [true; false] (length inp1 + 1) ++ List.repeat false (length inp2 + 1) /\
      output_neuron nc (inp1 ++ i :: inp2) 1 = repeat_seq _ [true; false] (length inp1) ++ List.repeat false (length inp2 + 2).
Proof.
  intros i inp1 inp2 n1 n2 nc Hinit HPos Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp1 Hinp2 Hi.
  rewrite <- Hid1 at 1.
  rewrite <- Hid2 at 3.
  induction inp1 as [|i1 inp1 IH].
  - simpl.
    rewrite Hid1, Hid2.
    apply (PL_Output_Amplifier_1_true_aux _ _ _ _ _ Hinit HPos Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp2 Hi).
  - destruct IH as [IH1 IH2]; [intros i0 Hin; apply Hinp1; now right|].
    assert (output_neuron nc ((i1 :: inp1) ++ i :: inp2) (Id (Feature n1)) = repeat_seq bool [true; false] (length (i1 :: inp1) + 1) ++
  repeat false (length inp2 + 1)) as H.
    * simpl.
      rewrite NstepsCircuit_output_neuron; trivial.
      rewrite Hid1.
      rewrite Hid1 in IH1.
      rewrite Hid2 in IH2.
      rewrite (curpot_sup_tauPL _ n2); trivial.
      rewrite Hinp1; [|now left].
      rewrite IH2.
      rewrite Nat.add_1_r, <- (repeat_seq_S_unfold _ false).
      simpl.
      f_equal.
      rewrite Nat.add_succ_r.
      simpl.
      now rewrite hd_app_alt.
      now rewrite repeat_seq_2_unfold, <- Nat.add_1_r.
    * split; trivial.
      rewrite <- Hid1 in Htau3.
      rewrite (One_Input_NC_delay_Int _ _ _ _ Hinit Hin2 Hin1 (One_Input_Or_Less_PL_1 _ _ _ Hid1 Hin2 Hid2 HPos)); trivial.
      rewrite H.
      rewrite ! Nat.add_1_r.
      rewrite <- (repeat_seq_S_unfold _ false).
      simpl.
      rewrite <- ! app_assoc, <- app_comm_cons.
      simpl.
      do 4 f_equal.
      rewrite ! ZL0, ! Nat.add_assoc, ! Nat.add_1_r.
      simpl.
      f_equal.
      now rewrite repeat_cons_same.
Qed.



(*** Negative Loop ***)


(** External input always true and oscilation **)

(* Case 1 : the weights of the first neuron are opposite value *)

Lemma NL_Output_Oscil_case1_aux : forall i inp n1 n2 nc l,
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Weights (Feature n1) 1 == - Weights (Feature n1) 2 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    (forall i', In i' (i :: inp) -> i' 2%nat = true) ->
    output_neuron nc inp 1 = false :: l ->
    output_neuron nc (i :: inp) 0 = true :: output_neuron nc inp (Id (Feature n1)).
Proof.
  intros i inp n1 n2 nc l Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Hinp Hout.
  rewrite <- Hid1.
  simpl.
  rewrite (proj1 (curpot_neuron_output_true _ _ _ _ Hin1)); [now f_equal|].
  rewrite NstepsCircuit_curpot_neuron; trivial.
  apply Qle_bool_iff.
  apply Qleb_plus_pos_r.
  - rewrite (potential_ti_sup_tau2 _ _ _ 1 2); trivial; [|now apply Hneg|rewrite ListNeuroLengthNL; trivial; apply Nat.lt_1_2|rewrite ListNeuroLengthNL; trivial; apply Nat.le_succ_diag_r|rewrite OneSupplementNL, ListNeuroLengthNL; trivial; now apply Two_Inputs_Two_Neurons].
    rewrite Hinp; [|now left].
    now rewrite Hout.
  - apply Qle_bool_iff.
    apply Qle_lteq.
    right.
    apply Qeq_sym.
    apply (fun H => if_curpot_sup_tau_eq_0_NL _ _ _ Hinit Hneg Hin1 Hid1 H Htau2 Htau1).
    intros i0 H.
    apply Hinp.
    now right.
Qed.



Lemma NL_Output_Oscil_case1_aux2 : forall i inp n1 n2 nc l,
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Weights (Feature n1) 1 == - Weights (Feature n1) 2 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    (forall i', In i' (i :: inp) -> i' 2%nat = true) ->
    output_neuron nc inp 1 = true :: l ->
    output_neuron nc (i :: inp) 0 = false :: output_neuron nc inp (Id (Feature n1)).
Proof.
  intros i inp n1 n2 nc l Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Hinp Hout.
  rewrite <- Hid1.
  simpl.
  rewrite (proj1 (curpot_neuron_output_false _ _ _ _ Hin1)); [now f_equal|].
  rewrite NstepsCircuit_curpot_neuron; trivial.
  apply Qlt_inf_0_trans_l.
  - apply Qle_bool_iff.
    rewrite (fun Hti => Qeq_bool_equiv_l _ _ _ (potential_ti _ 1 2 _ _ Hti)).
    rewrite ListNeuroLengthNL; trivial.
    rewrite (proj2 (Nat.ltb_lt _ _) Nat.lt_1_2).
    rewrite Nat.ltb_irrefl.
    rewrite Hinp; [|now left].
    rewrite Hout.
    apply Qle_bool_iff.
    apply Qle_lteq.
    right.
    simpl.
    apply (Qeq_trans _ (- Weights (Feature n1) 2 + Weights (Feature n1) 2)); [now apply Qplus_inj_r|apply (Qeq_trans _ _ _ (Qplus_comm _ _)); apply Qplus_opp_r].
    rewrite OneSupplementNL, ListNeuroLengthNL; trivial; now apply Two_Inputs_Two_Neurons.
  - apply (Qle_lt_trans _ 0).
    apply Qle_lteq.
    right.
    apply (fun H => if_curpot_sup_tau_eq_0_NL _ _ _ Hinit Hneg Hin1 Hid1 H Htau2 Htau1).
    intros i0 H.
    apply Hinp.
    now right.
    apply (Feature n1).
Qed.



Lemma NL_Output_Oscil_case1_aux3 : forall i4 inp n1 n2 nc l1 l2,
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Weights (Feature n1) 1 == - Weights (Feature n1) 2 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i', In i' (i4 :: inp) -> i' 2%nat = true) ->
    output_neuron nc inp 0 = false :: l1 ->
    output_neuron nc inp 1 = false :: l2 ->
    output_neuron nc (i4 :: inp) 0 = true :: false :: l1 /\ output_neuron nc (i4 :: inp) 1 = false :: false :: l2.
Proof.
  intros i4 inp n1 n2 nc l1 l2 Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp Hout1 Hout2.
  generalize Hout2; intros Hout2'.  
  generalize Htau3; intros Htau3'.
  rewrite <- Hid1 in Htau3'.
  assert (Hout7 := One_Input_NC_delay_Int _ _ inp _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau3').
  rewrite Hid2, Hid1 in Hout7.
  rewrite Hout1 in Hout7.
  simpl in Hout7.
  apply (NL_Output_Oscil_case1_aux i4 _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Hinp) in Hout2.
  rewrite Hid1, Hout1 in Hout2.
  assert (Hout3 := One_Input_NC_delay_Int _ _ (i4 :: inp) _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau3').
  rewrite Hid2, Hid1 in Hout3.
  rewrite Hout2 in Hout3.
  simpl in Hout3.
  rewrite <- Hout7, Hout2' in Hout3.
  now split.
Qed.



Lemma NL_Output_Oscil_case1_aux4 : forall i3 i4 inp n1 n2 nc l1 l2,
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Weights (Feature n1) 1 == - Weights (Feature n1) 2 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i', In i' (i3 :: i4 :: inp) -> i' 2%nat = true) ->
    output_neuron nc inp 0 = false :: l1 ->
    output_neuron nc inp 1 = false :: l2 ->
    output_neuron nc (i3 :: i4 :: inp) 0 = true :: true :: false :: l1 /\ output_neuron nc (i3 :: i4 :: inp) 1 = true :: false :: false :: l2.
Proof.
  intros i3 i4 inp n1 n2 nc l1 l2 Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp Hout1 Hout2.
  generalize Hout2; intros Hout2'.  
  generalize Htau3; intros Htau3'.
  rewrite <- Hid1 in Htau3'.
  destruct (fun H => NL_Output_Oscil_case1_aux3 i4 _ _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 H Hout1 Hout2) as [Hout4 Hout3].
  intros i' H'.
  apply Hinp.
  now right.
  assert (Hout7 := One_Input_NC_delay_Int _ _ inp _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau3').
  rewrite Hid2, Hid1 in Hout7.
  rewrite Hout1 in Hout7.
  simpl in Hout7.
  apply (NL_Output_Oscil_case1_aux i3 _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2) in Hout3; [|apply Hinp].
  rewrite Hid1, Hout4 in Hout3.
  assert (Hout5 := One_Input_NC_delay_Int _ _ (i3 :: i4 :: inp) _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau3').
  rewrite Hid2, Hid1 in Hout5.
  rewrite Hout3 in Hout5.
  simpl in Hout5.
  rewrite <- Hout7, Hout2' in Hout5.
  now split.
Qed.


Lemma NL_Output_Oscil_case1_aux5 : forall i2 i3 i4 inp n1 n2 nc l1 l2,
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Weights (Feature n1) 1 == - Weights (Feature n1) 2 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i', In i' (i2 :: i3 :: i4 :: inp) -> i' 2%nat = true) ->
    output_neuron nc inp 0 = false :: l1 ->
    output_neuron nc inp 1 = false :: l2 ->
    output_neuron nc (i2 :: i3 :: i4 :: inp) 0 = false :: true :: true :: false :: l1 /\ output_neuron nc (i2 :: i3 :: i4 :: inp) 1 = true :: true :: false :: false :: l2.
Proof.
  intros i2 i3 i4 inp n1 n2 nc l1 l2 Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp Hout1 Hout2.
  generalize Hout2; intros Hout2'.  
  generalize Htau3; intros Htau3'.
  rewrite <- Hid1 in Htau3'.
  destruct (fun H => NL_Output_Oscil_case1_aux4 i3 i4 _ _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 H Hout1 Hout2) as [Hout4 Hout3].
  intros i' H'.
  apply Hinp.
  now right.
  assert (Hout7 := One_Input_NC_delay_Int _ _ inp _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau3').
  rewrite Hid2, Hid1 in Hout7.
  rewrite Hout1 in Hout7.
  simpl in Hout7.
  apply (NL_Output_Oscil_case1_aux2 i2 _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2) in Hout3; [|apply Hinp].
  rewrite Hid1, Hout4 in Hout3.
  assert (Hout5 := One_Input_NC_delay_Int _ _ (i2 :: i3 :: i4 :: inp) _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau3').
  rewrite Hid2, Hid1 in Hout5.
  rewrite Hout3 in Hout5.
  simpl in Hout5.
  rewrite <- Hout7, Hout2' in Hout5.
  now split.
Qed.


Lemma NL_Output_Oscil_case1_aux6 : forall i1 i2 i3 i4 inp n1 n2 nc l1 l2,
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Weights (Feature n1) 1 == - Weights (Feature n1) 2 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i', In i' (i1 :: i2 :: i3 :: i4 :: inp) -> i' 2%nat = true) ->
    output_neuron nc inp 0 = false :: l1 ->
    output_neuron nc inp 1 = false :: l2 ->
    output_neuron nc (i1 :: i2 :: i3 :: i4 :: inp) 0 = false :: false :: true :: true :: false :: l1 /\ output_neuron nc (i1 :: i2 :: i3 :: i4 :: inp) 1 = false :: true :: true :: false :: false :: l2.
Proof.
  intros i1 i2 i3 i4 inp n1 n2 nc l1 l2 Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp Hout1 Hout2.
  generalize Hout2; intros Hout2'.  
  generalize Htau3; intros Htau3'.
  rewrite <- Hid1 in Htau3'.
  destruct (fun H => NL_Output_Oscil_case1_aux5 i2 i3 i4 _ _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 H Hout1 Hout2) as [Hout4 Hout3].
  intros i' H'.
  apply Hinp.
  now right.
  assert (Hout7 := One_Input_NC_delay_Int _ _ inp _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau3').
  rewrite Hid2, Hid1 in Hout7.
  rewrite Hout1 in Hout7.
  simpl in Hout7.
  apply (NL_Output_Oscil_case1_aux2 i1 _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2) in Hout3; [|apply Hinp].
  rewrite Hid1, Hout4 in Hout3.
  assert (Hout5 := One_Input_NC_delay_Int _ _ (i1 :: i2 :: i3 :: i4 :: inp) _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau3').
  rewrite Hid2, Hid1 in Hout5.
  rewrite Hout3 in Hout5.
  simpl in Hout5.
  rewrite <- Hout7, Hout2' in Hout5.
  now split.
Qed.



Theorem NL_Output_Oscil_case1 : forall inp n1 n2 nc,
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Weights (Feature n1) 1 == - Weights (Feature n1) 2 ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) 0 ->
    (forall i, In i inp -> i 2%nat = true) ->
    output_neuron nc inp 0 = repeat_seq _ [false; true; true; false] (length inp + 1) /\
      output_neuron nc inp 1 = repeat_seq _ [false; false; true; true] (length inp + 1).
Proof.
  intros inp n1 n2 nc Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp.
  rewrite Nat.add_1_r.
  simpl.
  assert (H := n_dec_4  (length inp)).
  destruct H as [q [r [H1 H2]]].
  rewrite H1.
  rewrite 2 repeat_decompose2; trivial.
  rewrite Nat.add_comm in H1.
  apply list_app_length in H1 as [l1 [l2 [H1 [H3 H4]]]].
  subst inp.
  assert (output_neuron nc l2 0 = [false] ++
                                          repeat_seq bool [false; true; true; false] (4 * q)  /\
            output_neuron nc l2 1 = [false] ++ repeat_seq bool [false; false; true; true] (4 * q)).
  - revert l2 Hinp H4.
    induction q as [|q IH]; intros l2 Hinp H4.
    * simpl.
      rewrite Nat.mul_0_r in H4.
      apply length_zero_iff_nil in H4.
      subst.
      rewrite <- Hid2, <- Hid1.
      split; rewrite output_neuron_Output; trivial; now apply (is_initial_output _ Hinit).
    * rewrite Nat.mul_succ_r.
      rewrite 2 (repeat_decompose2 _ _ q); trivial.
      set (n := (4 * q)%nat).
      rewrite Nat.mul_succ_r, Nat.add_comm in H4.
      apply list_app_length in H4 as [l3 [l4 [H4 [H5 H6]]]].
      subst.
      destruct l3 as [|hd1 [|hd2 [|hd3 [|hd4 [|hd5 tl]]]]]; try solve [inversion H5].
      simpl.
      apply (NL_Output_Oscil_case1_aux6 _ _ _ _ _ _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3); try solve [intros i' Hi'; apply Hinp; apply in_or_app; now right|apply IH; trivial; intros i Hi; apply in_app_or in Hi as [Hi|Hi]; apply Hinp; simpl; apply in_or_app; [now left|now do 5 right]].
  - assert (H5 := repeat_decompose _ [false] [true; true; false] 1 (4 * q)%nat); trivial.
    assert (H6 := repeat_decompose _ [false] [false; true; true] 1 (4 * q)%nat); trivial.
    simpl (repeat_seq _ _ 1) in H5, H6.
    simpl  ([_; _ ; _] ++ [_]) in H5, H6.
    simpl  ([_] ++ [ _ ; _ ; _]) in H5, H6.
    rewrite <- 2 app_assoc.
    rewrite Nat.add_comm in H5, H6.
    rewrite <- (app_nil_r [ _; _; _; _]) in H5.
    rewrite <- (app_nil_r [ _; _; _; true]) in H6.
    rewrite repeat_decompose2 in H5, H6; trivial.
    rewrite <- H5, <- H6; trivial.
    clear H5 H6.
    revert H.
    set (n := (4 * q)%nat).
    simpl.
    intros [Ha Hb].
    destruct r as [|[|[|[|r]]]].
    * simpl in H3.
      apply length_zero_iff_nil in H3.
      now subst.
    * simpl in H3.
      destruct l1 as [|hd [|hd' tl]]; try solve [inversion H3].
      now apply (NL_Output_Oscil_case1_aux3 _ _ _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp).
    * simpl in H3.
      destruct l1 as [|hd1 [|hd2 [|hd3 tl]]]; try solve [inversion H3].
      now apply (NL_Output_Oscil_case1_aux4 _ _ _ _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp).
    * simpl in H3.
      destruct l1 as [|hd1 [|hd2 [|hd3 [|hd4 tl]]]]; try solve [inversion H3].
      simpl.
      now apply (NL_Output_Oscil_case1_aux5 _ _ _ _ _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Hinp).
    * do 4 apply PeanoNat.lt_S_n in H2.
      now destruct (Nat.nlt_0_r r).
Qed.



(* Case 2 : the weights of the first neuron are more complexe *)


Lemma NL_Output_Oscil_case2_aux : forall i1 i2 i3 i4 inp n1 n2 nc l l',
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    0 <= Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2 ->
    (1 + Leak_Factor (Feature n1)) * (Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2) < Tau (Feature n1) ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) (Id (Feature n1)) ->
    (forall i', In i' (i1 :: i2 :: i3 :: i4 :: inp) -> i' 2%nat = true) ->
    output_neuron nc inp (Id (Feature n1)) = true :: l ->
    output_neuron nc inp (Id (Feature n2)) = false :: l' ->
    output_neuron nc (i1 :: i2 :: i3 :: i4 :: inp) (Id (Feature n1)) =  true :: false :: false :: true :: output_neuron nc inp (Id (Feature n1))/\
      output_neuron nc (i1 :: i2 :: i3 :: i4 :: inp) (Id (Feature n2)) = false :: false :: true :: true :: output_neuron nc inp (Id (Feature n2)).
Proof.
  intros i1 i2 i3 i4 inp n1 n2 nc l l' Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4 Hinp Hout1 Hout2.
  assert (output_neuron nc (i4 :: inp) (Id (Feature n1)) = true :: output_neuron nc inp (Id (Feature n1))) as Hout3.
  apply curpot_neuron_output_true; trivial.
  rewrite Hid1.
  apply curpot_sup_tauNL; trivial; try solve [now rewrite <- Hid2, Hout2|now rewrite <- Hid1].
  apply Hinp.
  do 3 right; now left.
  rewrite <- Hid1.
  apply (Qle_trans _ (Tau (Feature n1))).
  apply Qlt_le_weak.
  apply (Feature n1).
  apply curpot_neuron_output_true_2; trivial.
  exists l; trivial.
  assert (output_neuron nc (i4 :: inp) (Id (Feature n2)) = true :: output_neuron nc inp (Id (Feature n2))) as Hout4.
  rewrite NstepsCircuit_output_neuron; trivial.
  f_equal.
  apply Qle_bool_iff.
  apply curpot_neuron_output_true_2; trivial.
  rewrite (One_Input_NC_delay_Int _ _ (i4 :: inp) _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau4).
  rewrite Hout3, Hout1.
  exists (l ++ [false]); trivial.
  assert (curpot_neuron nc (i3 :: i4 :: inp) 0 ==
  Weights (Feature n1) 1 + Weights (Feature n1) 2) as Hcur1.
  apply curpot_sup_tauNL_2; trivial; try solve [apply Hinp; do 2 right;now left| now rewrite <- Hid2 at 1|now rewrite <- Hid2, Hout4 at 1].
  rewrite <- Hid1.
  apply curpot_neuron_output_true; trivial.
  assert (output_neuron nc (i3 :: i4 :: inp) (Id (Feature n1)) = false :: output_neuron nc (i4 :: inp) (Id (Feature n1))) as Hout5.
  apply curpot_neuron_output_false; trivial.
  rewrite Hid1.
  apply (fun H => Qlt_eq_l _ _ _ H (Qeq_sym _ _ Hcur1)).
  rewrite <- Hid2 at 1.
  assert (H0 := proj1 (LeakRange (Feature n1))).
  apply Qmul_more_1_le in Htau2; trivial.
  assert (output_neuron nc (i3 :: i4 :: inp) (Id (Feature n2)) = true :: output_neuron nc (i4 :: inp) (Id (Feature n2))) as Hout6.
  rewrite NstepsCircuit_output_neuron; trivial.
  f_equal.
  apply Qle_bool_iff.
  apply curpot_neuron_output_true_2; trivial.
  rewrite (One_Input_NC_delay_Int _ _ (i3 :: i4 :: inp) _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau4).
  rewrite Hout5, Hout3.
  exists (output_neuron nc inp (Id (Feature n1)) ++ [false]); trivial.
  assert (curpot_neuron nc (i2 :: i3 :: i4 :: inp) 0 == (1 + Leak_Factor (Feature n1)) * (Weights (Feature n1) 1 + Weights (Feature n1) 2)) as Hcur2.
  apply curpot_sup_tauNL_3; trivial; try solve [apply Hinp; right; now left|now rewrite <- Hid2 at 1|now rewrite <- Hid2, Hout6].
  assert (output_neuron nc (i2 :: i3 :: i4 :: inp) (Id (Feature n1)) = false :: output_neuron nc (i3 :: i4 :: inp) (Id (Feature n1))) as Hout7.
  apply curpot_neuron_output_false; trivial.
  rewrite Hid1.
  apply (Qlt_eq_l _ _ _ Htau2).
  apply Qeq_sym.
  now rewrite Hid2.
  assert (output_neuron nc (i2 :: i3 :: i4 :: inp) (Id (Feature n2)) = false :: output_neuron nc (i3 :: i4 :: inp) (Id (Feature n2))) as Hout8.
  rewrite NstepsCircuit_output_neuron; trivial.
  f_equal.
  apply Qleb_lt.
  apply curpot_neuron_output_false_2; trivial.
  rewrite (One_Input_NC_delay_Int _ _ (i2 :: i3 :: i4 :: inp) _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau4).
  rewrite Hout7, Hout5.
  exists (output_neuron nc (i4 :: inp) (Id (Feature n1)) ++ [false]); trivial.
  assert (output_neuron nc (i1 :: i2 :: i3 :: i4 :: inp) (Id (Feature n1)) = true :: output_neuron nc (i2 :: i3 :: i4 :: inp) (Id (Feature n1))) as Hout9.
  apply curpot_neuron_output_true; trivial.
  rewrite Hid1.
  apply curpot_sup_tauNL; trivial; try solve [apply Hinp; now left|now rewrite <- Hid2, Hout8, Hout6].
  apply (fun H => Qle_eq_r _ _ _ H (Qeq_sym _ _ Hcur2)).
  apply Qmult_le_0_compat; [|now rewrite <- Hid2 at 1].
  apply Qle_plus_pos_r; [apply Z.le_0_1|apply (Feature n1)].
  split; [now rewrite Hout9, Hout7, Hout5, Hout3|].
  rewrite NstepsCircuit_output_neuron; trivial.
  f_equal.
  apply Qleb_lt.
  apply curpot_neuron_output_false_2; trivial.
  rewrite (One_Input_NC_delay_Int _ _ (i1 :: i2 :: i3 :: i4 :: inp) _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau4).
  rewrite Hout9, Hout7.
  exists (output_neuron nc (i3 :: i4 :: inp) (Id (Feature n1)) ++ [false]); trivial.
  now rewrite Hout8, Hout6, Hout4.
Qed.


Lemma NL_Output_Oscil_case2_aux2 : forall inp1 inp2 m n1 n2 nc l l',
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    0 <= Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2 ->
    (1 + Leak_Factor (Feature n1)) * (Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2) < Tau (Feature n1) ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) (Id (Feature n1)) ->
    (forall i', In i' (inp1 ++ inp2) -> i' 2%nat = true) ->
    output_neuron nc inp2 (Id (Feature n1)) = true :: l ->
    output_neuron nc inp2 (Id (Feature n2)) = false :: l' ->
    (length inp1 = 4 * m)%nat ->
    output_neuron nc (inp1 ++ inp2) (Id (Feature n1)) = repeat_seq _ [true; true; false; false] (length inp1 + 1) ++ l /\ output_neuron nc (inp1 ++ inp2) (Id (Feature n2)) = repeat_seq _ [false; true; true; false] (length inp1 + 1) ++ l'.
Proof.
  intros inp1 inp2 m n1 n2 nc l l' Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4 Hinp Hout1 Hout2 Hlen.
  revert inp1 Hinp Hlen.
  induction m as [|m IH]; intros inp1 Hinp Hlen.
  - apply length_zero_iff_nil in Hlen.
    split; now subst.
  - rewrite Nat.mul_succ_r in Hlen.
    rewrite Hlen.
    rewrite <- Nat.add_assoc.
    rewrite 2 (repeat_decompose2 _ _ m); trivial.
    rewrite Nat.add_comm in Hlen.
    apply list_app_length in Hlen as [l3 [l4 [H4 [H5 H6]]]].
    rewrite H4.
    destruct l3 as [|hd1 [|hd2 [|hd3 [|hd4 [|hd5 tl]]]]]; try solve [inversion H5].
    rewrite <- app_assoc.
    specialize (IH l4).
    rewrite H6 in IH.
    destruct IH as [IH1 IH2]; trivial.
    intros i' H.
    apply Hinp.
    subst.
    do 4 right; trivial.
    rewrite (repeat_decompose2 _ _ m) in IH1; trivial.
    rewrite (repeat_decompose2 _ _ m) in IH2; trivial.
    revert IH1 IH2.
    set (q := (4 * m)%nat).
    simpl.
    intros IH1 IH2.
    rewrite <- IH1, <- IH2.
    revert IH1 IH2.
    apply (NL_Output_Oscil_case2_aux _ _ _ _ _ _ _ _ _ _ Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4).
    intros i' H.
    apply Hinp.
    now rewrite H4.
Qed.


Lemma NL_Output_Oscil_case2_aux3 : forall inp1 inp2 m r n1 n2 nc l l',
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    0 <= Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2 ->
    (1 + Leak_Factor (Feature n1)) * (Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2) < Tau (Feature n1) ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) (Id (Feature n1)) ->
    (forall i', In i' (inp1 ++ inp2) -> i' 2%nat = true) ->
    output_neuron nc inp2 (Id (Feature n1)) = true :: l ->
    output_neuron nc inp2 (Id (Feature n2)) = false :: l' ->
    (length inp1 = 4 * m + r)%nat ->
    (r < 4)%nat ->
    output_neuron nc (inp1 ++ inp2) (Id (Feature n1)) = repeat_seq _ [true; true; false; false] (length inp1 + 1) ++ l /\ output_neuron nc (inp1 ++ inp2) (Id (Feature n2)) = repeat_seq _ [false; true; true; false] (length inp1 + 1) ++ l'.
Proof.
  intros inp1 inp2 m r n1 n2 nc l l' Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4 Hinp Hout1 Hout2 Hlen Hr.
  generalize Hlen; intros Hlen2.
  rewrite Nat.add_comm in Hlen2.
  apply list_app_length in Hlen2 as [l3 [l4 [H4 [H5 H6]]]].
  destruct l3 as [|hd1 [|hd2 [|hd3 [|hd4 tl]]]]; try solve [inversion H5].
  - apply (NL_Output_Oscil_case2_aux2 inp1 inp2 m n1 n2 nc l l' Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4 Hinp Hout1 Hout2).
    now subst inp1.
  - destruct (fun Hinp => NL_Output_Oscil_case2_aux2 ((fun _ : nat => true) :: (fun _ : nat => true) :: (fun _ : nat => true) ::  inp1) inp2 (m + 1) n1 n2 nc l l' Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4 Hinp Hout1 Hout2) as [H H0].
    intros i' [H|[H|[H|H]]]; try now subst.
    now apply Hinp.
    simpl (length _).
    rewrite Nat.mul_add_distr_l.
    rewrite Hlen.
    rewrite <- H5.
    rewrite <- 3 Nat.add_1_r.
    now rewrite <- 3 Nat.add_assoc.
    simpl.
    rewrite <- 3 app_comm_cons in H.
    rewrite 3 NstepsCircuit_output_neuron in H; trivial.
    rewrite <- 3 app_comm_cons in H0.
    rewrite 3 NstepsCircuit_output_neuron in H0; trivial.
    simpl (length _) in H, H0.
    rewrite Nat.add_succ_l in H, H0.
    rewrite <- (repeat_seq_S_4_unfold _ false) in H, H0.
    rewrite (Nat.add_succ_l (S (length inp1)) 1) in H, H0.
    rewrite <- (repeat_seq_S_4_unfold _ false _ _ _ _ (S (length inp1) + 1)) in H.
    rewrite <- (repeat_seq_S_4_unfold _ false _ _ _ _ (S (length inp1) + 1)) in H0.
    rewrite (Nat.add_succ_l (length inp1) 1) in H, H0.
    rewrite <- (repeat_seq_S_4_unfold _ false _ _ _ _ (length inp1 + 1)) in H.
    rewrite <- (repeat_seq_S_4_unfold _ false _ _ _ _ (length inp1 + 1)) in H0.
    inversion H.
    now inversion H0.
  - destruct (fun Hinp => NL_Output_Oscil_case2_aux2 ((fun _ : nat => true) :: (fun _ : nat => true) ::  inp1) inp2 (m + 1) n1 n2 nc l l' Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4 Hinp Hout1 Hout2) as [H H0].
    intros i' [H|[H|H]]; try now subst.
    now apply Hinp.
    simpl (length _).
    rewrite Nat.mul_add_distr_l.
    rewrite Hlen.
    rewrite <- H5.
    rewrite <- 2 Nat.add_1_r.
    now rewrite <- 2 Nat.add_assoc.
    simpl.
    rewrite <- 2 app_comm_cons in H.
    rewrite 2 NstepsCircuit_output_neuron in H; trivial.
    rewrite <- 2 app_comm_cons in H0.
    rewrite 2 NstepsCircuit_output_neuron in H0; trivial.
    simpl (length _) in H, H0.
    rewrite Nat.add_succ_l in H, H0.
    rewrite <- (repeat_seq_S_4_unfold _ false) in H, H0.
    rewrite (Nat.add_succ_l (length inp1) 1) in H, H0.
    rewrite <- (repeat_seq_S_4_unfold _ false _ _ _ _ (length inp1 + 1)) in H.
    rewrite <- (repeat_seq_S_4_unfold _ false _ _ _ _ (length inp1 + 1)) in H0.
    inversion H.
    now inversion H0.
  - destruct (fun Hinp => NL_Output_Oscil_case2_aux2 ((fun _ : nat => true) :: inp1) inp2 (m + 1) n1 n2 nc l l' Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4 Hinp Hout1 Hout2) as [H H0].
    intros i' [H|H].
    now subst.
    now apply Hinp.
    simpl (length _).
    rewrite Nat.mul_add_distr_l.
    rewrite Hlen.
    now rewrite <- H5, <- Nat.add_1_r, <- Nat.add_assoc.
    rewrite <- app_comm_cons in H.
    rewrite NstepsCircuit_output_neuron in H; trivial.
    rewrite <- app_comm_cons in H0.
    rewrite NstepsCircuit_output_neuron in H0; trivial.
    simpl (length _) in H, H0.
    rewrite Nat.add_succ_l in H, H0.
    rewrite <- (repeat_seq_S_4_unfold _ false) in H, H0.
    inversion H.
    now inversion H0.
  - rewrite <- H5 in Hr.
    simpl in Hr.
    do 4 apply PeanoNat.lt_S_n in Hr.
    now destruct (Nat.nlt_0_r (length tl)).
Qed.


Theorem NL_Output_Oscil_case2 : forall inp n1 n2 nc,
    is_initial nc ->
    NegativeLoop nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    0 <= Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2 ->
    (1 + Leak_Factor (Feature n1)) * (Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2) < Tau (Feature n1) ->
    Tau (Feature n1) <= Weights (Feature n1) 2 ->
    Tau (Feature n2) <= Weights (Feature n2) (Id (Feature n1)) ->
    (forall i', In i' inp -> i' 2%nat = true) ->
    output_neuron nc inp (Id (Feature n1)) = repeat_seq _ [false; true; true; false] (length inp + 1) /\ output_neuron nc inp (Id (Feature n2)) = repeat_seq _ [false; false; true; true] (length inp + 1).
Proof.
  intros inp n1 n2 nc Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4 Hinp.
  assert (output_neuron nc [] (Id (Feature n1)) = [false] /\ output_neuron nc [] (Id (Feature n2)) = [false]).
  simpl.
  rewrite ! output_neuron_Output; trivial.
  split; now apply (is_initial_output _ Hinit).
  assert (forall i1, In i1 inp -> output_neuron nc [i1] (Id (Feature n1)) =
                                    repeat_seq bool [false; true; true; false] (length [i1] + 1)).
  - intros i1 Hinpi1.
    destruct H as [H1 H2].
    rewrite NstepsCircuit_output_neuron; trivial.
    rewrite NstepsCircuit_curpot_neuron; trivial.
    assert (Hcur := is_initial_curpot _ Hinit _ Hin1).
    rewrite <- (curpot_neuron_CurPot _ _ Hin1) in Hcur.
    rewrite Hcur.
    rewrite (proj2 (Qleb_lt _ _) (PosTau _)).
    simpl.
    f_equal; trivial.
    apply Qle_bool_iff.
    apply Qle_plus_pos_r.
    rewrite (OneSupplementNL _ Hneg), (ListNeuroLengthNL _ Hneg).
    apply (potential_sup_tau_or_0_input_false _ _ (Id (Feature n2)) 2); trivial.
    rewrite Hid2 at 1.
    simpl.
    now rewrite H2.
    rewrite Nat.ltb_irrefl.
    now apply Hinp.
    rewrite Hid2.
    now apply Two_Inputs_Two_Neurons.
    apply Qmul_more_1_le in Htau2; trivial.
    apply Qmult_le_0_compat.
    apply LeakRange.
    apply Qle_lteq.
    right.
    now apply Qeq_sym.
    apply (Feature n1).
  - assert (forall i1, In i1 inp ->  output_neuron nc [i1] (Id (Feature n2)) = repeat_seq bool [false; false; true; true] (length [i1] + 1)).
    * intros i1 Hinpi1.
      specialize (H0 _ Hinpi1).
      assert (Hout3 := One_Input_NC_delay_Int _ _ [i1] _ Hinit Hin2 Hin1 (One_Input_Or_Less_NL_1 _ _ _ Hid1 Hin2 Hid2 Hneg) Htau4).
      now rewrite H0 in Hout3.
    * assert (Hleninp := eq_refl (length inp)).
      revert Hleninp.
      set (n := length inp) at 2.
      intros Hleninp.
      destruct n as [|[|n]].
      -- apply length_zero_iff_nil in Hleninp.
         now subst.
      -- apply length_S_last_elt in Hleninp as [x [l [H2 H3]]].
         apply length_zero_iff_nil in H3.
         subst.
         split; [apply H0|apply H1]; now left.
      -- apply length_S_last_elt in Hleninp as [i1 [l [Hleninp1 Hleninp2]]].
         subst inp.
         destruct (n_dec_4 (length l)) as [q [r [Hlen Hlen2]]].
         destruct (NL_Output_Oscil_case2_aux3 l [i1] q r n1 n2 nc (repeat_seq bool [false; false; true; true] (length [i1])) (repeat_seq bool [false; true; true; false] (length [i1])) Hinit Hneg Hin1 Hid1 Hin2 Hid2 Htau1 Htau2 Htau3 Htau4) as [H4 H5]; trivial.
         apply H0.
         apply in_or_app.
         right; now left.
         apply H1.
         apply in_or_app.
         right; now left.
         simpl in H4.
         rewrite app_length.
         rewrite Nat.add_1_r.
         now split.
Qed.



(**Property : Contralateral Inhibition -- Winner Takes All**)
(* External inputs are always true *)

Lemma CI_Output_Oscil_aux : forall inp n1 n2 nc,
    is_initial nc ->
    ContraInhib nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2 ->
    (forall i, In i inp -> i 2%nat = true) ->
    output_neuron nc inp 0 = repeat true (length inp) ++ false :: nil.
Proof.
  intros inp n1 n2 nc Hinit Hci Hin1 Hid1 _ Hid2 Htau Hi.
  rewrite <- Hid1.
  induction inp as [|i inp IH].
  - rewrite output_neuron_Output; trivial.
    apply (is_initial_output _ Hinit _ Hin1).
  - simpl.
    rewrite (proj1 (curpot_neuron_output_true _ _ _ _ Hin1)).
    f_equal.
    apply IH.
    intros i0 Hi0.
    apply Hi.
    now right.
    rewrite Hid1.
    rewrite Hid2 in Htau.
    apply (curpot_sup_tauCI _ n2); trivial.
Qed.



Lemma CI_Output_Oscil_aux2 : forall i n1 n2 nc,
    is_initial nc ->
    ContraInhib nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2 -> 
    Tau (Feature n2) <= Weights (Feature n2) 3 ->
    i 2%nat = true ->
    i 3%nat = true ->
    output_neuron nc [i] (Id (Feature n2)) = true :: false :: nil.
Proof.
  intros i n1 n2 nc Hinit Hci Hin1 Hid1 Hin2 Hid2 Htau3 Htau4 Hi1 Hi2.
  rewrite (proj1 (curpot_neuron_output_true _ _ _ _ Hin2)); [f_equal; rewrite output_neuron_Output; trivial; apply (is_initial_output _ Hinit _ Hin2)|].
  rewrite NstepsCircuit_curpot_neuron; trivial.
  rewrite curpot_neuron_CurPot; trivial.
  rewrite (is_initial_curpot _ Hinit); trivial.
  rewrite (proj2 (Qleb_lt _ _) (PosTau _)).
  apply Qle_plus_pos_r.
  rewrite (OneSupplementCI _ Hci), (ListNeuroLengthCI _ Hci).    
  apply (potential_sup_tau_or_0_input_false _ _ (Id (Feature n1)) 3); trivial.
  rewrite Hid1 at 1.
  simpl.
  rewrite output_neuron_Output; trivial.
  now rewrite (is_initial_output _ Hinit).
  apply (Two_Inputs_Two_Neurons4 _ _ nc); trivial.
  now apply Hci.
  apply Qmult_le_0_compat.
  apply (Feature n2).
  rewrite (is_initial_curpot _ Hinit); trivial.
  apply Qle_refl.
Qed.



Lemma CI_Output_Oscil_aux3 : forall i1 i2 n1 n2 nc,
    is_initial nc ->
    ContraInhib nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2 -> 
    Tau (Feature n2) <= Weights (Feature n2) 3 ->
    Weights (Feature n2) (Id (Feature n1)) + Weights (Feature n2) 3 <= 0 ->
    i1 2%nat = true ->
    i1 3%nat = true ->
    i2 2%nat = true ->
    i2 3%nat = true ->
    output_neuron nc [i1; i2] (Id (Feature n2)) = false :: true :: false :: nil.
Proof.
  intros i1 i2 n1 n2 nc Hinit Hci Hin1 Hid1 Hin2 Hid2 Htau3 Htau4 Htau5 Hi11 Hi12 Hi21 Hi22.
  rewrite NstepsCircuit_output_neuron; trivial.
  f_equal.
  apply Qleb_lt.
  rewrite Hid2.
  apply (curpot_sup_tauCI_2 _ n1); trivial; try solve [now rewrite Hid1 in Htau5].
  rewrite (CI_Output_Oscil_aux [i2] _ _ _ Hinit Hci Hin1 Hid1 Hin2 Hid2 Htau3); trivial.
  intros i [Hi|Hi]; [now subst|inversion Hi].
  now apply (CI_Output_Oscil_aux2 _ n1).
Qed.


Lemma CI_Output_Oscil_aux4 : forall i inp n1 n2 l l' nc,
    is_initial nc ->
    ContraInhib nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2 -> 
    Tau (Feature n2) <= Weights (Feature n2) 3 ->
    Weights (Feature n2) (Id (Feature n1)) + Weights (Feature n2) 3 <= 0 ->
    (forall i', In i' (i :: inp) -> i' 2%nat = true /\ i' 3%nat = true) ->
    output_neuron nc inp (Id (Feature n1)) = true :: l ->
    output_neuron nc inp (Id (Feature n2)) = false :: l' ->
    output_neuron nc (i :: inp) (Id (Feature n2)) = false :: output_neuron nc inp (Id (Feature n2)).

Proof.
  intros i inp n1 n2 l l' nc Hinit Hci Hin1 Hid1 Hin2 Hid2 Htau3 Htau4 Htau5 Hinp Hout1 Hout2.
  apply curpot_neuron_output_false; trivial.
  rewrite Hid2.
  apply (curpot_sup_tauCI_2 _ n1); trivial; try solve [now rewrite Hid1 in Htau5].
  apply Hinp.
  now left.
  rewrite Hid1 in Hout1.
  now rewrite Hout1.
Qed.


Theorem CI_Winner_Takes_All : forall inp n1 n2 nc,
    is_initial nc ->
    ContraInhib nc ->
    In n1 (ListNeuro nc) ->
    Id (Feature n1) = 0%nat ->
    In n2 (ListNeuro nc) ->
    Id (Feature n2) = 1%nat ->
    Tau (Feature n1) <= Weights (Feature n1) (Id (Feature n2)) + Weights (Feature n1) 2 -> 
    Tau (Feature n2) <= Weights (Feature n2) 3 ->
    Weights (Feature n2) (Id (Feature n1)) + Weights (Feature n2) 3 <= 0 ->
    (forall i', In i' inp -> i' 2%nat = true /\ i' 3%nat = true) ->
    output_neuron nc inp (Id (Feature n1)) = repeat true (length inp) ++ false :: nil  /\ output_neuron nc inp (Id (Feature n2)) = if (length inp =? 0)%nat then [false] else repeat false (length inp - 1) ++ true :: false :: nil .
Proof.
  intros inp n1 n2 nc Hinit Hci Hin1 Hid1 Hin2 Hid2 Htau3 Htau4 Htau5 Hinp.
  split.
  - rewrite Hid1.
    apply (CI_Output_Oscil_aux _ n1 n2); trivial.
    intros i' Hi'.
    now apply Hinp.   
  - induction inp as [|i1 [|i2 [|i3 inp]] IH].
    * rewrite output_neuron_Output; [rewrite (is_initial_output _ Hinit)|];trivial.
    * apply (CI_Output_Oscil_aux2 _ n1); trivial; try solve [apply Hinp; now left].
    * apply (CI_Output_Oscil_aux3 _ _ n1); trivial; try solve [apply Hinp; now left|apply Hinp; right; now left].
    * simpl.
      simpl in IH.
      rewrite (CI_Output_Oscil_aux4 _ _ n1 _ (true :: repeat true (length inp) ++ false :: nil) (repeat false (length inp) ++ [true; false])); trivial; [simpl; f_equal| |]; try solve [apply IH; intros i0 [Hi0|[Hi0|Hi0]]; subst; apply Hinp; [right; now left|do 2 right; now left|now do 3 right]].
      rewrite Hid1.
      rewrite (CI_Output_Oscil_aux _ n1 n2); trivial.
      intros i Hi.
      apply Hinp.
      now right.
Qed.
