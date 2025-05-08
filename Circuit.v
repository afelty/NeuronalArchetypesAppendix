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
Require Import Facts Neuron SortList.


(*Neuronal Circuit*)

(* Description of a neuronal circuit *)
Record NeuroCircuit :=
  MakeCircuit {
      Time : nat;
      ListNeuro : list Neuron;
      SupplInput : nat;
      IdNeuroDiff : forall n m l1 l2 l3,
        ListNeuro = l1 ++ n :: l2 ++ m :: l3 -> Id (Feature n) <> Id (Feature m);        
      IdInfLen : forall n,
        In n ListNeuro ->
        (Id (Feature n) < length ListNeuro)%nat;        
      TimeNeuro : forall n,
        In n ListNeuro ->
        length (Output n) = (Time + 1)%nat; 
    }.




(** Properties of existence in a neuronal circuit nc of a neuron that have an identifier < length (ListNeuro nc)) and unicity of an identifier for a neuron a circuit **)


(*Sorting a neuronal circuit*)


Lemma exists_sorted_nc_part : forall nc,
  exists nc',
    Sorted (fun x y => (Id (Feature x) < Id (Feature y))%nat) (ListNeuro nc') /\
      (forall n, In n (ListNeuro nc) <-> In n (ListNeuro nc')) /\
      length (ListNeuro nc) = length (ListNeuro nc').
Proof.
  intros nc.
  assert (forall n m l1 l2 l3,
             sort_list _ (ListNeuro nc) (fun x => Id (Feature x)) =
               l1 ++ n :: l2 ++ m :: l3 -> Id (Feature n) <> Id (Feature m)) as H.
  - intros n m l1 l2 l3 H.
    apply sort_list_app_inj2 in H as [l1' [l2' [l3' [H|H]]]].
    now apply IdNeuroDiff in H.
    apply IdNeuroDiff in H.
    now apply not_eq_sym.
  - assert (forall n : Neuron,
               In n (sort_list _ (ListNeuro nc) (fun x => Id (Feature x))) ->
               (Id (Feature n) < length (sort_list _ (ListNeuro nc) (fun x => Id (Feature x))))%nat) as H0.
    * intros x Hin.
      apply sort_list_in in Hin.
      rewrite <- sort_list_length.
      now apply IdInfLen.
    * assert (forall n : Neuron,
                 In n (sort_list _ (ListNeuro nc) (fun x => Id (Feature x))) ->
                 length (Output n) = (Time nc + 1)%nat) as H1.
      -- intros x Hin.
         apply sort_list_in in Hin.
         now apply TimeNeuro.
      -- exists (MakeCircuit (Time nc) (sort_list _ (ListNeuro nc) (fun x => Id (Feature x))) (SupplInput nc) H H0 H1 ).
         unfold ListNeuro at 1 4 7.
         split; [|split; [apply sort_list_in|apply sort_list_length]].
         clear H H0 H1.
         specialize (IdNeuroDiff nc) as H.
         induction (ListNeuro nc) as [|hd tl IH].
         apply Sorted_nil.
         simpl.
         apply sort_list_aux_sorted.
         intros n Hin.
         apply sort_list_in in Hin.
         apply in_split in Hin as [l1 [l2 Hin]].
         subst.
         apply (H _ _ [] l1 l2); trivial.
         apply IH.
         intros n m l1 l2 l3 H0.
         apply (H _ _ (hd :: l1) l2 l3).
         subst.
         apply app_comm_cons.
Qed.



Lemma len_inf_in_listneuro : forall id nc,
    (id < length (ListNeuro nc))%nat ->
    exists n, In n (ListNeuro nc) /\ Id (Feature n) = id.
Proof.
  intros id nc Hlen.
  assert (Hsort := exists_sorted_nc_part nc).
  destruct Hsort as [nc' [Hsort [Hin Hlen2]]].
  rewrite Hlen2 in Hlen.
  assert (exists n : Neuron, In n (ListNeuro nc') /\ Id (Feature n) = id) as H.
  - assert (Hinf := IdInfLen nc').
    clear Hlen2 Hin.
    revert Hlen.
    assert (Hn := Nat.eq_refl (length (ListNeuro nc'))).
    revert Hn.
    set (n:= length (ListNeuro nc')) at 2.
    clearbody n.
    revert Hsort Hinf.
    set (l := ListNeuro nc'). 
    clearbody l.
    revert l.
    induction n as [|m IH]; intros l Hsort Hinf Hlen H.
    * apply length_zero_iff_nil in Hlen. subst.
      now destruct (Nat.nlt_0_r id).
    * apply length_S_last_elt in Hlen as [y [l3 [H0 H1]]].
      subst l.
      rewrite app_length in H.
      rewrite Nat.add_1_r in H.
      apply PeanoNat.lt_n_Sm_le in H.
      apply Nat.le_lteq in H as [H0|H0].
      -- apply Sorted_app1 in Hsort as Hsort'.
         apply IH in Hsort'; trivial.
         destruct Hsort' as [n [Hsort1 Hsort2]].
         exists n.
         split; trivial.
         apply in_or_app; now left.
         intros x H2.
         assert (Id (Feature y) < length (l3 ++ [y]))%nat.
         apply (Hinf y).
         apply in_or_app; right; now left.
         assert (Id (Feature x) < Id (Feature y))%nat.
         apply in_split in H2 as [l4 [l5 Hin]].
         subst.
         rewrite <- ! app_assoc in Hsort.
         apply Sorted_app2 in Hsort.
         rewrite <- app_comm_cons in Hsort.
         apply Sorted_extends in Hsort as H4; [|intros x' y' z; apply Nat.lt_trans].
         apply (proj1 (Forall_forall _ _)) with y in H4; trivial.
         apply in_or_app.
         right; now left.
         apply Nat.le_succ_l in H3.
         apply (Nat.le_lt_trans _ _ _ H3) in H.
         rewrite app_length in H.
         rewrite Nat.add_1_r in H.
         apply Nat.le_succ_l.
         now apply PeanoNat.lt_S_n.
      -- exists y; split.
         apply in_or_app; right; now left.
         rewrite H0.
         symmetry.
         apply (sorted_eq_length_fst_eq _ (fun x => Id (Feature x)) y l3 []); trivial.
  - destruct H as [n [H H0]].
    exists n; split; trivial.
    now apply Hin.
Qed.


Lemma same_id_same_neuron : forall n1 n2 nc,
    In n1 (ListNeuro nc) ->
    In n2 (ListNeuro nc) ->
    Id (Feature n1) = Id (Feature n2) ->
    n1 = n2.
Proof.
  intros n1 n2 nc Hn1 Hn2 Hid.
  apply in_split in Hn1 as [l1 [l2 Hn1]].
  rewrite Hn1 in Hn2.
  apply in_app_or in Hn2 as [Hn2|Hn2].
  - apply in_split in Hn2 as [la [lb Hn2]].
    subst.
    rewrite <- app_assoc, <- app_comm_cons in Hn1.
    destruct (IdNeuroDiff nc n2 n1 la lb l2).
    rewrite Hn1.
    now repeat rewrite map_app, map_cons.
    now symmetry.
  - destruct Hn2 as [Hn2|Hn2]; trivial.
    apply in_split in Hn2 as [la [lb Hn2]].
    subst.
    destruct (IdNeuroDiff nc n1 n2 l1 la lb); trivial.
Qed.



(*Initialization of the circuit *)

Definition is_initial (nc : NeuroCircuit) :=
  forall n, In n (ListNeuro nc) -> is_initial_neuro n (length (ListNeuro nc) + SupplInput nc).

Lemma is_initial_output : forall nc,
    is_initial nc ->
    forall n, In n (ListNeuro nc) -> Output n = [false].
Proof.
  intros nc H n Hin.
  apply H in Hin as [nf Hin].
  now rewrite (proj1 (proj2 Hin)).
Qed.

Lemma is_initial_curpot : forall nc,
    is_initial nc ->
    forall n, In n (ListNeuro nc) -> CurPot n == 0.
Proof.
  intros nc H x Hin.
  apply H in Hin as [nf Hin].
  now rewrite (proj2 (proj2 Hin)).
Qed.


Lemma is_initial_time : forall nc,
    is_initial nc ->
    (0 < length (ListNeuro nc))%nat ->
    Time nc = 0%nat.
Proof.
  intros nc H Hlen.
  apply len_inf_in_listneuro in Hlen as [n [Hin Hid]].
  apply is_initial_output in Hin as Hout; trivial.
  assert (length (Output n) = 0 + 1)%nat as H0.
  now rewrite Hout.
  rewrite (TimeNeuro _ _ Hin) in H0.
  now apply Nat.add_cancel_r in H0.
Qed.


(** Apply an external input to the circuit**)

(* time = 0 / a neuron *)

Definition output_neuron_init nc id :=
  match find (fun x => Id (Feature x) =? id)%nat (ListNeuro nc) with
  |Some x => Output x
  |None => []
  end.


(* time + 1 / on a neuron of the circuit *)

Definition NextNeuroInNC (nc : NeuroCircuit) (inp : nat -> bool) := NextNeuron (fun x => if (x <? length (ListNeuro nc))%nat then hd false (output_neuron_init nc x) else inp x) (length (ListNeuro nc) + SupplInput nc).


Definition NextListNeuro (nc : NeuroCircuit) (inp : nat -> bool) := (map (NextNeuroInNC nc inp) (ListNeuro nc)).


Lemma NextNeuroInNC_neuro_same_feature : forall nc inp n,
    Feature (NextNeuroInNC nc inp n) = Feature n.
Proof.
  intros nc inp n.
  unfold NextNeuroInNC.
  apply next_neuro_same_feature.
Qed.


Lemma id_neuro_diff_next : forall (nc : NeuroCircuit) inp (n m : Neuron) (l1 l2 l3 : list Neuron),
    NextListNeuro nc inp = l1 ++ n :: l2 ++ m :: l3 ->
    Id (Feature n) <> Id (Feature m).
Proof.
  intros nc inp n m l1 l2 l3 H.
  unfold NextListNeuro in H.
  apply map_list_app_inj in H as [n' [l1' [l [H [H1 [H2 H3]]]]]].
  apply map_list_app_inj in H2 as [m' [l2' [l3' [H2 [H4 [H5 H6]]]]]].
  subst.
  apply IdNeuroDiff in H.
  now rewrite 2 NextNeuroInNC_neuro_same_feature.
Qed.


Lemma id_inf_numb_neuron_next : forall (nc : NeuroCircuit) inp (n : Neuron),
    In n (NextListNeuro nc inp) ->
    (Id (Feature n) < length (NextListNeuro nc inp))%nat.
Proof.
  intros nc inp n H.
  unfold NextListNeuro in *.
  rewrite map_length.
  apply in_map_iff in H as [n0 [H H0]].
  subst.
  apply IdInfLen in H0.
  now rewrite NextNeuroInNC_neuro_same_feature.
Qed.


Lemma next_time : forall nc inp n,
    In n (NextListNeuro nc inp) ->
    length (Output n) = (Time nc + 1 + 1)%nat.
Proof.
  intros nc inp n H.
  unfold NextListNeuro in *.
  apply in_map_iff in H as [n0 [H H0]].
  apply (TimeNeuro nc) in H0.
  subst.
  unfold NextNeuron, Output at 1.
  simpl.
  rewrite H0.
  now rewrite 2 Nat.add_1_r.
Qed.


Lemma nextlistneurp_time0 : forall nc inp n,
    (Time nc + 1)%nat = 0%nat -> In n (NextListNeuro nc inp) -> Output n = [false].
Proof.
  intros nc inp n H.
  rewrite Nat.add_1_r in H.
  inversion H.
Qed.



(* time + 1 / on the circuit *)

Definition NextStepC (nc : NeuroCircuit) inp :=
  let listneuro := NextListNeuro nc inp in
  MakeCircuit (Time nc + 1)%nat listneuro (SupplInput nc) (id_neuro_diff_next nc inp) (id_inf_numb_neuron_next nc inp) (next_time _ _).


(* time + n / on the circuit *)

Fixpoint NstepsCircuit (nc: NeuroCircuit) (inp: list (nat -> bool)) : NeuroCircuit :=
  match inp with
  | nil => nc
  | h::tl => (NextStepC (NstepsCircuit nc tl) h) 
  end.

Lemma listneuro_nstep_length : forall inp nc,
    length (ListNeuro (NstepsCircuit nc inp)) = length (ListNeuro nc).
Proof.
  intros inp nc.
  induction inp as [|i inp IH]; trivial.
  simpl.
  unfold NextListNeuro.
  now rewrite map_length.
Qed.

Lemma listneuro_nstep_supplinput : forall inp nc,
    SupplInput (NstepsCircuit nc inp) = SupplInput nc.
Proof.
  intros inp nc.
  induction inp as [|i inp IH]; trivial.
Qed.


(* time + n / a neuron *)

Definition output_neuron nc inp id :=
  match find (fun x => Id (Feature x) =? id)%nat (ListNeuro (NstepsCircuit nc inp)) with
  |Some x => Output x
  |None => []
  end.


Definition curpot_neuron nc inp id :=
  match find (fun x => Id (Feature x) =? id)%nat (ListNeuro (NstepsCircuit nc inp)) with
  |Some x => CurPot x
  |None => 0
  end.




(** Well-formedness circuit**)  


Definition well_formed_circuit nc :=
  (forall n : Neuron, In n (ListNeuro nc) -> well_formed_neuron n).



Lemma well_formed_nstep : forall inp nc,
    well_formed_circuit nc ->
    well_formed_circuit (NextStepC nc inp).
Proof.
  intros inp nc H n Hin.
  simpl in Hin.
  unfold NextListNeuro in Hin.
  apply in_map_iff in Hin as [n' [Hin1 Hin2]].
  subst.
  apply H in Hin2.
  unfold NextNeuroInNC.
  now apply well_formed_nextneuron.
Qed.


Lemma well_formed_nstepcir : forall inp nc,
    well_formed_circuit nc ->
    well_formed_circuit (NstepsCircuit nc inp).
Proof.
  intros inp nc H.
  induction inp as [|i inp IH]; trivial.
  simpl.
  now apply well_formed_nstep.
Qed.



(* Intermediate properties *)


Lemma find_neuro_in : forall n nc,
    In n (ListNeuro nc) ->
    find (fun x : Neuron => Id (Feature x) =? Id (Feature n))%nat (ListNeuro nc) = Some n.
Proof.
  intros n nc H.
  case_eq (find (fun x : Neuron => Id (Feature x) =? Id (Feature n))%nat (ListNeuro nc)).
  - intros n0 Hn.
    apply find_some in Hn as [Hn1 Hn2].
    apply Nat.eqb_eq in Hn2.
    now rewrite (same_id_same_neuron _ _ _ Hn1 H Hn2).
  - intros Hn.
    apply (find_none _ _) with n in Hn; trivial.
    apply Nat.eqb_neq in Hn.
    now destruct Hn.
Qed.


Lemma find_neuro_in_alt : forall n nc nf,
    In n (ListNeuro nc) ->
    nf = Feature n ->
    find (fun x : Neuron => Id (Feature x) =? Id nf)%nat (ListNeuro nc) = Some n.
Proof.
  intros n nc nf H H0.
  subst.
  now apply find_neuro_in.
Qed.


Lemma curpot_neuron_CurPot : forall n nc,
    In n (ListNeuro nc) ->
    curpot_neuron nc [] (Id (Feature n)) = CurPot n.
Proof.
  intros n nc H.
  unfold curpot_neuron.
  simpl.
  now rewrite (find_neuro_in _ _ H).
Qed.


Lemma output_neuron_Output : forall n nc,
    In n (ListNeuro nc) ->
    output_neuron nc [] (Id (Feature n)) = Output n.
Proof.
  intros n nc H.
  unfold output_neuron.
  simpl.
  now rewrite (find_neuro_in _ _ H).
Qed.


Lemma in_listneuro_nstepnc : forall n nc inp,
    In n (ListNeuro nc) ->
    exists n',
      In n' (ListNeuro (NstepsCircuit nc inp)) /\
        Feature n = Feature n' /\
        Output n' = output_neuron nc inp (Id (Feature n)) /\
        CurPot n' = curpot_neuron nc inp (Id (Feature n)).
Proof.
  intros n nc inp H.
  induction inp as [|i inp IH].
  - exists n; repeat split; trivial.
    unfold output_neuron.
    simpl.
    rewrite find_neuro_in; trivial.
    unfold curpot_neuron.
    simpl.
    rewrite find_neuro_in; trivial.
  - simpl.
    unfold NextListNeuro.
    destruct IH as [n1 [IH1 [IH2 [IH3 IH4]]]].
    exists (NextNeuron
              (fun x : nat =>
                 if (x <? length (ListNeuro (NstepsCircuit nc inp)))%nat
                 then List.hd false (output_neuron nc inp x)
                 else i x)
              (length (ListNeuro (NstepsCircuit nc inp)) +
                 SupplInput (NstepsCircuit nc inp)) n1).
    repeat split.
    * now apply in_map.
    * now rewrite next_neuro_same_feature.
    * unfold output_neuron.
      rewrite IH2.
      rewrite <- (next_neuro_same_feature (fun x : nat => if (x <? length (ListNeuro (NstepsCircuit nc inp)))%nat then List.hd false (output_neuron nc inp x) else i x) n1 (length (ListNeuro (NstepsCircuit nc inp)) + SupplInput (NstepsCircuit nc inp))).
      rewrite find_neuro_in; trivial.
      simpl.
      unfold NextListNeuro at 1, NextNeuroInNC.
      now apply in_map.
    * unfold curpot_neuron.
      rewrite IH2.
      rewrite <- (next_neuro_same_feature (fun x : nat => if (x <? length (ListNeuro (NstepsCircuit nc inp)))%nat then List.hd false (output_neuron nc inp x) else i x) n1 (length (ListNeuro (NstepsCircuit nc inp)) + SupplInput (NstepsCircuit nc inp))).
      rewrite find_neuro_in; trivial.
      simpl.
      unfold NextListNeuro at 1, NextNeuroInNC.
      now apply in_map.        
Qed.


(** Unfolding functions output_neuron and curpot_neuron **)


Lemma NstepsCircuit_curpot_neuron : forall nc i inp n,
    In n (ListNeuro nc) ->
    curpot_neuron nc (i :: inp) (Id (Feature n)) ==
      potential (Weights (Feature n))
                (fun x : nat =>
                   if (x <? length (ListNeuro nc))%nat
                   then hd false (output_neuron nc inp x)
                   else i x)
                (length (ListNeuro nc) +
                   SupplInput nc) +
        (if Tau (Feature n) <=? curpot_neuron nc inp (Id (Feature n))
         then 0
         else Leak_Factor (Feature n) * curpot_neuron nc inp (Id (Feature n))).
Proof.
  intros nc i inp n Hin.
  unfold curpot_neuron.
  apply (in_listneuro_nstepnc _ _ (i :: inp)) in Hin as [n' [Hin1 [Hin2 [Hin3 Hin4]]]].
  apply find_neuro_in in Hin1 as H.
  rewrite Hin2.
  rewrite H.
  simpl in Hin1.
  unfold NextListNeuro in Hin1.
  apply in_map_iff in Hin1 as [n1 [H1 H2]].
  apply find_neuro_in in H2.
  subst.
  rewrite NextNeuroInNC_neuro_same_feature.
  rewrite H2.
  unfold NextNeuroInNC.
  rewrite listneuro_nstep_length, listneuro_nstep_supplinput.
  simpl.
  unfold NextPotential.
  assert (potential (Weights (Feature n1))
      (fun x : nat =>
       if (x <? length (ListNeuro nc))%nat
       then List.hd false (output_neuron nc inp x)
       else i x) (length (ListNeuro nc) + SupplInput nc) ==
            potential (Weights (Feature n1))
    (fun x : nat =>
     if (x <? length (ListNeuro nc))%nat
     then hd false (output_neuron nc inp x)
     else i x) (length (ListNeuro nc) + SupplInput nc)) as Hpot.
  apply potential_equiv_inp.
  intros m Hm.
  case_eq (m <? length (ListNeuro nc))%nat; intros Hlen; trivial.
  case_eq (Tau (Feature n1) <=? CurPot n1); intros H0.
  apply (Qeq_trans _ _ _ Hpot).
  symmetry.
  apply Qplus_0_r.
  now apply Qplus_inj_r.
Qed.


Lemma NstepsCircuit_output_neuron : forall nc i inp n,
    In n (ListNeuro nc) ->
    output_neuron nc (i :: inp) (Id (Feature n)) =
      (Tau (Feature n) <=? curpot_neuron nc (i :: inp) (Id (Feature n)))
        :: output_neuron nc inp (Id (Feature n)).
Proof.
  intros nc i inp n Hin.
  apply (in_listneuro_nstepnc _ _ inp) in Hin as [n' [Hin1 [Hin2 [_ Hcur]]]].
  unfold output_neuron.
  unfold curpot_neuron.
  rewrite Hin2.
  rewrite (find_neuro_in _ _ Hin1).
  apply (in_map (NextNeuroInNC (NstepsCircuit nc inp) i)) in Hin1.
  apply (find_neuro_in _  (NstepsCircuit nc (i :: inp))) in Hin1 as H.
  rewrite NextNeuroInNC_neuro_same_feature in H.
  now rewrite H.
Qed.


(** Link between curpot_neuron and output_neuron **)


Lemma curpot_neuron_output_true : forall nc i inp n,
    In n (ListNeuro nc) ->
    Tau (Feature n) <= curpot_neuron nc (i::inp) (Id (Feature n)) <->
      output_neuron nc (i :: inp) (Id (Feature n)) = true :: output_neuron nc inp (Id (Feature n)).
Proof.
  intros nc i inp n Hin.
  split.
  - intros Hcur.
    rewrite NstepsCircuit_output_neuron; trivial.
    f_equal.
    now apply Qle_bool_iff.
  - intros Hout.
    rewrite NstepsCircuit_output_neuron in Hout; trivial.
    inversion Hout.
    now apply Qle_bool_iff.
Qed.


Lemma curpot_neuron_output_false : forall nc i inp n,
    In n (ListNeuro nc) ->
    curpot_neuron nc (i::inp) (Id (Feature n)) < Tau (Feature n) <->
      output_neuron nc (i :: inp) (Id (Feature n)) = false :: output_neuron nc inp (Id (Feature n)).
Proof.
  intros nc i inp n Hin.
  split.
  - intros Hcur.
    rewrite NstepsCircuit_output_neuron; trivial.
    f_equal.
    now apply Qleb_lt.
  - intros Hout.
    rewrite NstepsCircuit_output_neuron in Hout; trivial.
    inversion Hout.
    now apply Qleb_lt.
Qed.


Lemma curpot_neuron_output_true_2 : forall nc inp n,
    In n (ListNeuro nc) ->
    is_initial nc ->
    Tau (Feature n) <= curpot_neuron nc inp (Id (Feature n)) <->
      exists l, output_neuron nc inp (Id (Feature n)) = true :: l.
Proof.
  intros nc [|i inp] n Hin Hinit.
  split.
  - intros H.
    rewrite (curpot_neuron_CurPot _ _ Hin) in H.
    apply (fun H => Qle_eq_r _ _ _ H (is_initial_curpot _ Hinit _ Hin)) in H.
    apply Qle_not_lt in H.
    destruct H.
    apply (Feature n).
  - intros [l H].
    rewrite (output_neuron_Output _ _ Hin) in H.
    rewrite (is_initial_output _ Hinit _ Hin) in H.
    inversion H.
  - split; intros H.
    exists (output_neuron nc inp (Id (Feature n))).
    now apply curpot_neuron_output_true.
    destruct H as [l H].
    apply curpot_neuron_output_true; trivial.
    rewrite H.
    rewrite NstepsCircuit_output_neuron in H; trivial.
    now inversion H.
Qed.


Lemma curpot_neuron_output_false_2 : forall nc inp n,
    In n (ListNeuro nc) ->
    is_initial nc ->
    curpot_neuron nc inp (Id (Feature n)) < Tau (Feature n) <->
      exists l, output_neuron nc inp (Id (Feature n)) = false :: l.
Proof.
  intros nc [|i inp] n Hin Hinit.
  split.
  - intros H.
    rewrite (output_neuron_Output _ _ Hin).
    rewrite (is_initial_output _ Hinit _ Hin).
    exists []; trivial.
  - intros [l H].
    rewrite (curpot_neuron_CurPot _ _ Hin).
    apply (fun H => Qlt_eq_l _ _ _ H (Qeq_sym _ _ (is_initial_curpot _ Hinit _ Hin))).
    apply (Feature n).
  - split; intros H.
    exists (output_neuron nc inp (Id (Feature n))).
    now apply curpot_neuron_output_false.
    destruct H as [l H].
    apply curpot_neuron_output_false; trivial.
    rewrite H.
    rewrite NstepsCircuit_output_neuron in H; trivial.
    now inversion H.
Qed.



(* Single-input current potential and output *)


Lemma curpot_cons_oi : forall id i inp n nc,
    One_Input_Or_Less (Feature n) id (length (ListNeuro nc) + SupplInput nc) ->
    In n (ListNeuro nc) ->
    curpot_neuron nc (i :: inp) (Id (Feature n)) ==
      (if
          if (id <? length (ListNeuro nc))%nat
          then hd false (output_neuron nc inp id)
          else i id
      then Weights (Feature n) id
      else 0) + (if Tau (Feature n) <=? curpot_neuron nc inp (Id (Feature n))
   then 0
   else Leak_Factor (Feature n) * curpot_neuron nc inp (Id (Feature n))).
Proof.
  intros id i inp n nc Hoi Hin.
  revert i.
  induction inp as [|i' inp IH]; intros i.
  - rewrite NstepsCircuit_curpot_neuron; trivial.
    apply Qplus_inj_r.
    now rewrite (potential_oi _ _ _ _ Hoi).
  - rewrite NstepsCircuit_curpot_neuron; trivial.
    apply Qplus_inj_r.
    now rewrite potential_oi.
Qed.



Lemma curpot_cons_w_greater_tau_oi : forall id i inp n nc,
    One_Input_Or_Less (Feature n) id (length (ListNeuro nc) + SupplInput nc) ->
    Tau (Feature n) <= Weights (Feature n) id ->
    is_initial nc ->
    In n (ListNeuro nc) ->
    curpot_neuron nc (i :: inp) (Id (Feature n)) ==
      if if (id <? length (ListNeuro nc))%nat
          then hd false (output_neuron nc inp id)
          else i id
      then Weights (Feature n) id
      else 0.
Proof.
  intros id i inp n nc Hoi H Hinit Hin.
  revert i.
  induction inp as [|i' inp IH]; intros i.
  - apply (Qeq_trans _ _ _ (curpot_cons_oi _ _ _ _ _ Hoi Hin)).
    rewrite curpot_neuron_CurPot; trivial.
    apply (is_initial_curpot _ Hinit) in Hin as Hinit'.
    rewrite ! (Qeq_bool_equiv_r _ _ _ Hinit').
    apply Qeq_sym.
    apply Qeq_plus_0_l_eq.
    apply Qplus_inj_l; apply Qeq_sym.
    rewrite if_false_r; [|apply Qleb_lt; apply (Feature n)].
    apply mul_0_iff.
    now right.
  -  apply (Qeq_trans _ _ _ (curpot_cons_oi _ _ _ _ _ Hoi Hin)).
    apply Qeq_sym.
    apply Qeq_plus_0_l_eq.
    apply Qplus_inj_l; apply Qeq_sym.
    case_eq (Tau (Feature n) <=? curpot_neuron nc (i' :: inp) (Id (Feature n))); intros H0.
    apply Qeq_refl.
    apply mul_0_iff.
    right.
    rewrite IH.
    case_eq (if (id <? length (ListNeuro nc))%nat
    then hd false (output_neuron nc inp id)
    else i' id); intros H1; [|apply Qeq_refl].
    rewrite ! (Qeq_bool_equiv_r _ _ _ (IH _)), H1 in H0.
    apply Qle_bool_iff in H.
    rewrite H0 in H.
    inversion H.
Qed.



Lemma output_cons_w_greater_tau_oi : forall id i inp n nc,
    One_Input_Or_Less (Feature n) id (length (ListNeuro nc) + SupplInput nc) ->
    Tau (Feature n) <= Weights (Feature n) id ->
    is_initial nc ->
    In n (ListNeuro nc) ->
    output_neuron nc (i :: inp) (Id (Feature n)) = (if (id <? length (ListNeuro nc))%nat
          then hd false (output_neuron nc inp id)
          else i id) :: output_neuron nc inp (Id (Feature n)).
Proof.
  intros id i inp n nc Hoi H Hinit Hin.
  rewrite NstepsCircuit_output_neuron; trivial.
  f_equal.
  rewrite (Qeq_bool_equiv_r _ _ _ (curpot_cons_w_greater_tau_oi _ _ _ _ _ Hoi H Hinit Hin)).
  case_eq (if (id <? length (ListNeuro nc))%nat
     then hd false (output_neuron nc inp id)
     else i id); intros H1.
  now apply Qle_bool_iff.
  apply Qleb_lt.
  apply (Feature n).
Qed.




(* Equivalence between circuits *)

Definition EquivNeuroCircuit nc1 nc2 :=
  Time nc1 = Time nc2 /\
    length (ListNeuro nc1) = length (ListNeuro nc2) /\
    (forall n1 n2, In n1 (ListNeuro nc1) -> In n2 (ListNeuro nc2) ->
                   Id (Feature n1) = Id (Feature n2) ->
                   EquivNeuron n1 n2 (length (ListNeuro nc1) + SupplInput nc1)%nat) /\
    SupplInput nc1 = SupplInput nc2.


(** Reflexivity **)

Lemma EquivNeuroCircuit_refl : forall nc,              
    EquivNeuroCircuit nc nc.
Proof.
  intros nc.
  repeat split; trivial; assert (H2 := same_id_same_neuron _ _ _ H H0 H1); intros; subst n1; trivial; apply Qeq_refl.
Qed.


(** Symmetry **)

Lemma EquivNeuroCircuit_sym : forall nc1 nc2,              
    EquivNeuroCircuit nc1 nc2 ->
    EquivNeuroCircuit nc2 nc1.
Proof.
  intros nc1 nc2 [Htime [Hlen [Hneur Hsuppl]]].
  split; [|split; [|split]]; try solve [now symmetry].
  intros n1 n2 H H0 H1.
  symmetry in H1; specialize (Hneur _ _ H0 H H1).
  rewrite Hlen, Hsuppl in Hneur.
  now apply EquivNeuron_sym.
Qed.


(** Transitivity **)

Lemma EquivNeuroCircuit_trans : forall nc1 nc2 nc3,              
    EquivNeuroCircuit nc1 nc2 ->
    EquivNeuroCircuit nc2 nc3 ->
    EquivNeuroCircuit nc1 nc3.
Proof.
  intros nc1 nc2 nc3 [Htime1 [Hlen1 [Hneur1 Hsuppl1]]] [Htime2 [Hlen2 [Hneur2 Hsuppl2]]].
  split; [|split; [|split]].
  - now rewrite Htime1.
  - now rewrite Hlen1.
  - intros n1 n3 H H0 H1.
    apply IdInfLen in H as H2.
    rewrite Hlen1 in H2.
    apply len_inf_in_listneuro in H2 as [n2 [H2 H3]].
    symmetry in H3.
    rewrite H3 in H1.
    specialize (Hneur1 _ _ H H2 H3).
    specialize (Hneur2 _ _ H2 H0 H1).
    rewrite <- Hlen1, <- Hsuppl1 in Hneur2.
    revert Hneur1 Hneur2.
    apply EquivNeuron_trans.
  - now rewrite Hsuppl1.
Qed.


Lemma curpot_output_neuron_Equiv : forall nc1 nc2 inp n,
    (n < length (ListNeuro nc1))%nat ->
    EquivNeuroCircuit nc1 nc2 ->
    curpot_neuron nc1 inp n == curpot_neuron nc2 inp n /\ output_neuron nc1 inp n = output_neuron nc2 inp n.
Proof.
  intros nc1 nc2 inp n H [Ha [Hb [Hc Hd]]].
  revert n H. induction inp as [|i inp IH]; intros n H.
  - generalize H; intros H0.
    rewrite Hb in H0.
    apply len_inf_in_listneuro in H as [n1 [H1 H2]].
    apply len_inf_in_listneuro in H0 as [n2 [H3 H4]].
    subst.
    split.
    * unfold curpot_neuron.
      simpl.
      rewrite (find_neuro_in _ _ H1).
      rewrite <- H4.
      rewrite (find_neuro_in _ _ H3).
      apply Hc; trivial.
      now symmetry.
    * unfold output_neuron.
      simpl.
      rewrite (find_neuro_in _ _ H1).
      rewrite <- H4.
      rewrite (find_neuro_in _ _ H3).
      apply Hc; trivial.
      now symmetry.
  - generalize H; intros H0.
    generalize H; intros Hlen.
    rewrite Hb in H0.
    apply len_inf_in_listneuro in H as [n1 [H1 H2]].
    apply len_inf_in_listneuro in H0 as [n2 [H3 H4]].
    subst.
    rewrite <- H4 at 2 4.
    assert (curpot_neuron nc1 (i :: inp) (Id (Feature n1)) ==
              curpot_neuron nc2 (i :: inp) (Id (Feature n2))).
    * rewrite 2 NstepsCircuit_curpot_neuron; trivial.
      symmetry in H4.
      apply (Hc _ _ H1 H3) in H4 as [[H4a [H4b [H4c H4d]]] [H5 H6]].
      rewrite <- H4a.
      rewrite (Qeq_bool_equiv _ _ _ _ H4d (proj1 (IH _ Hlen))).
      assert (potential (Weights (Feature n1))
    (fun x : nat =>
     if (x <? length (ListNeuro nc1))%nat
     then List.hd false (output_neuron nc1 inp x)
     else i x) (length (ListNeuro nc1) + SupplInput nc1) ==
  potential (Weights (Feature n2))
    (fun x : nat =>
     if (x <? length (ListNeuro nc2))%nat
     then List.hd false (output_neuron nc2 inp x)
     else i x) (length (ListNeuro nc2) + SupplInput nc2)) as Hpot.
      apply (Qeq_trans _ _ _ (potential_equiv_weight _ (Weights (Feature n2)) _ _ H4b)).
      rewrite <- Hb, <- Hd.
      apply potential_equiv_inp.
      intros m H.
      case_eq (m <? length (ListNeuro nc1))%nat; intros H'; trivial.
      apply Nat.ltb_lt in H'.
      f_equal.
      now apply IH.
      destruct (Tau (Feature n2) <=? curpot_neuron nc2 inp (Id (Feature n1))).
      -- now apply Qplus_inj_r.
      -- apply Qeq_plus_compat; trivial.
         apply Qeq_mul_compat; trivial.
         now apply IH.
    * split; trivial.
      case_eq (curpot_neuron nc1 (i :: inp) (Id (Feature n1)) <? Tau (Feature n1)); intros H0.
      -- apply Qltb_lt in H0.
         rewrite (proj1 (curpot_neuron_output_false _ _ _ _ H1) H0).
         apply (Qlt_eq_l _ _ _ H0) in H.
         symmetry in H4.
         destruct (Hc _ _ H1 H3 H4) as [[_ [_ [_ Htau]]] [_ _]].
         apply (Qlt_eq_r _ _ _ H) in Htau.
         rewrite (proj1 (curpot_neuron_output_false _ _ _ _ H3) Htau).
         f_equal.
         rewrite <- H4.
         apply IH.
         now apply IdInfLen.
      -- apply Qltb_ge in H0.
         rewrite (proj1 (curpot_neuron_output_true _ _ _ _ H1) H0).
         apply (Qle_eq_r _ _ _ H0) in H.
         symmetry in H4.
         destruct (Hc _ _ H1 H3 H4) as [[_ [_ [_ Htau]]] [_ _]].
         apply (Qle_eq_l _ _ _ H) in Htau.
         rewrite (proj1 (curpot_neuron_output_true _ _ _ _ H3) Htau).
         f_equal.
         rewrite <- H4.
         apply IH.
         now apply IdInfLen.
Qed.



Lemma EquivNeuroCircuit_NextStepC : forall nc1 nc2 inp,
    EquivNeuroCircuit nc1 nc2 ->
    EquivNeuroCircuit (NextStepC nc1 inp) (NextStepC nc2 inp).
Proof.
  intros nc1 nc2 inp Hcir.
  generalize Hcir; intros [H1 [H2 [H3 H4]]].
  split; [|split; [|split]]; trivial.
  - simpl. now rewrite H1.
  - simpl. unfold NextListNeuro.
    now rewrite ! map_length.
  - intros n1 n2 H H0 H6.
    simpl in H, H0.
    unfold NextListNeuro in H, H0.
    apply in_map_iff in H as [n3 [Ha Hb]].
    apply in_map_iff in H0 as [n4 [Hc Hd]].
    subst.
    simpl in H6.
    simpl.
    unfold NextListNeuro.
    rewrite map_length.
    specialize (H3 _ _ Hb Hd H6).
    repeat split; try solve [now apply H3].
    * unfold NextNeuroInNC.
      assert (H7 := nextneuron_equiv _ _ (fun x : nat =>
                                            if (x <? length (ListNeuro nc1))%nat then hd false (output_neuron_init nc1 x) else inp x) (length (ListNeuro nc1) + SupplInput nc1) H3).
      rewrite (proj1 (proj2 H7)).
      clear H7.
      rewrite <- H2, <- H4.
      apply (fun H => proj1 (proj2 (nextneuron_equiv_inp _ _ _ _ H))).
      intros m H.
      case_eq (m <? length (ListNeuro nc1))%nat; intros H'; trivial.
      f_equal.
      apply Nat.ltb_lt in H'.
      now apply (curpot_output_neuron_Equiv _ _ [] _ H') in Hcir as [_ Hcir].
    * unfold NextNeuroInNC.
      assert (H7 := nextneuron_equiv _ _ (fun x : nat =>
                                            if (x <? length (ListNeuro nc1))%nat then hd false (output_neuron_init nc1 x) else inp x) (length (ListNeuro nc1) + SupplInput nc1) H3).
      rewrite (proj2 (proj2 H7)).
      clear H7.
      rewrite <- H2, <- H4.
      apply (fun H => proj2 (proj2 (nextneuron_equiv_inp _ _ _ _ H))).
      intros m H.
      case_eq (m <? length (ListNeuro nc1))%nat; intros H'; trivial.
      f_equal.
      apply Nat.ltb_lt in H'.
      now apply (curpot_output_neuron_Equiv _ _ [] _ H') in Hcir as [_ Hcir].
Qed.


Lemma EquivNeuroCircuit_NstepsCircuit : forall nc1 nc2 inp,
    EquivNeuroCircuit nc1 nc2 ->
    EquivNeuroCircuit (NstepsCircuit nc1 inp) (NstepsCircuit nc2 inp).
Proof.
  intros nc1 nc2 inp H.
  induction inp as [|i inp IH]; trivial.
  simpl.
  now apply EquivNeuroCircuit_NextStepC.
Qed.




(** Equivalence for curpot/output between function for a neuron and for a neuron in a circuit **)


Fixpoint inp_mult inp nc:=
  match inp with
  | nil => nil
  | i :: inp => (fun x : nat =>
                   if (x <? length (ListNeuro nc))%nat
                   then hd false (output_neuron nc inp x)
                   else i x) :: inp_mult inp nc
  end.

Lemma inp_mult_unfold : forall inp nc,
    inp_mult inp nc =
      match inp with
      | nil => nil
      | i :: inp => (fun x : nat =>
                       if (x <? length (ListNeuro nc))%nat
                       then hd false (output_neuron nc inp x)
                       else i x) :: inp_mult inp nc
      end.
Proof.
  intros [|i inp] nc; trivial.
Qed.




Lemma curpot_neuron_nstep : forall nc inp n,
    In n (ListNeuro nc) ->
    curpot_neuron nc inp (Id (Feature n)) == CurPot (AfterNstepsNeuron n (inp_mult inp nc) (length (ListNeuro nc) + SupplInput nc)%nat).
Proof.
  intros nc inp n Hin.
  induction inp as [|i inp IH].
  - unfold curpot_neuron.
    simpl.
    rewrite (find_neuro_in _ _ Hin).
    apply Qeq_refl.
  - rewrite NstepsCircuit_curpot_neuron; trivial.
    simpl.
    unfold NextPotential.
    rewrite ! after_nsteps_same_feature.
    rewrite <- (Qeq_bool_equiv_r _ _ _ IH).
    case_eq (Tau (Feature n) <=? curpot_neuron nc inp (Id (Feature n))); intros H1.
    apply Qplus_0_r.
    apply Qplus_inj_l.
    apply Qeq_mul_compat_r; trivial.
Qed.


Lemma output_neuron_nstep : forall nc inp n,
    In n (ListNeuro nc) ->
    output_neuron nc inp (Id (Feature n)) = Output (AfterNstepsNeuron n (inp_mult inp nc) (length (ListNeuro nc) + SupplInput nc)).
Proof.
  intros nc inp n Hin.
  induction inp as [|i inp IH].
  - unfold output_neuron.
    simpl.
    now rewrite (find_neuro_in _ _ Hin).
  - assert (H := curpot_neuron_nstep _ (i :: inp) _ Hin).
    case_eq (Tau (Feature n) <=? curpot_neuron nc (i :: inp) (Id (Feature n))); intros H0.
    * apply Qle_bool_iff in H0.
      rewrite (proj1 (curpot_neuron_output_true _ _ _ _ Hin) H0).
      apply (fun H' => Qle_eq_r _ _ _ H' H) in H0.
      rewrite inp_mult_unfold.
      rewrite inp_mult_unfold in H0.
      rewrite (proj1 (AfterNSN_curpot_output_true _ _ _ _) H0).
      now f_equal.
    * apply Qleb_lt in H0.
      rewrite (proj1 (curpot_neuron_output_false _ _ _ _ Hin) H0).
      apply (fun H' => Qlt_eq_l _ _ _ H' H) in H0. 
      rewrite inp_mult_unfold.
      rewrite inp_mult_unfold in H0.
      rewrite (proj1 (AfterNSN_curpot_output_false _ _ _ _) H0).
      now f_equal.
Qed.



(** One-input neuron **)

(* External input *)

Lemma curpot_neuron_nstep_oi_ext : forall nc id inp n,
    In n (ListNeuro nc) ->
    One_Input_Or_Less (Feature n) id (length (ListNeuro nc) + SupplInput nc) ->
    (length (ListNeuro nc) <= id)%nat ->
    curpot_neuron nc inp (Id (Feature n)) == CurPot (AfterNstepsNeuron n inp (length (ListNeuro nc) + SupplInput nc)).
Proof.
  intros nc id inp n Hin Hoi Hid.
  induction inp as [|i inp IH].
  now rewrite (curpot_neuron_CurPot  _ _ Hin).
  apply (Qeq_trans _ _ _ (curpot_cons_oi _ _ _ _ _ Hoi Hin)).
  rewrite (CurPot_cons_oi _ _ _ _ _ Hoi).
  apply Nat.ltb_ge in Hid.
  rewrite Hid.
  apply Qplus_inj_l.
  rewrite (Qeq_bool_equiv_r _ _ _ IH).
  destruct (Tau (Feature n) <=?
              CurPot (AfterNstepsNeuron n inp (length (ListNeuro nc) + SupplInput nc))).
  apply Qeq_refl.
  now apply Qeq_mul_compat_r.
Qed.


Lemma output_neuron_nstep_oi_ext : forall nc id inp n,
    In n (ListNeuro nc) ->
    One_Input_Or_Less (Feature n) id (length (ListNeuro nc) + SupplInput nc) ->
    (length (ListNeuro nc) <= id)%nat ->
    output_neuron nc inp (Id (Feature n)) = Output (AfterNstepsNeuron n inp (length (ListNeuro nc) + SupplInput nc)).
Proof.
  intros nc id inp n Hin Hoi Hid.
  induction inp as [|i inp IH].
  now rewrite (output_neuron_nstep _ _ _ Hin).
  rewrite NstepsCircuit_output_neuron; trivial.
  rewrite AfterNSN_curpot_output_unfold.
  f_equal.
  apply Qeq_bool_equiv_r.
  apply (curpot_neuron_nstep_oi_ext _ id); trivial.
  apply IH.
Qed.


(* Internal input *)

Lemma curpot_neuron_nstep_oi_int : forall nc i id inp n,
    is_initial nc ->
    In n (ListNeuro nc) ->
    One_Input_Or_Less (Feature n) id (length (ListNeuro nc) + SupplInput nc) ->
    (id < length (ListNeuro nc))%nat ->
    curpot_neuron nc (i :: inp) (Id (Feature n)) == CurPot (AfterNstepsNeuron n (map (fun i => (fun x => i)) (output_neuron nc inp id)) (length (ListNeuro nc) + SupplInput nc)).
Proof.
  intros nc i id inp n Ht0 Hin Hoi Hid.
  generalize Hid; intros Hidn.
  apply len_inf_in_listneuro in Hidn as [n' [Hinn' Hidn']].
  subst id.
  revert i.
  induction inp as [|i' inp IH]; intros i; apply (Qeq_trans _ _ _ (curpot_cons_oi _ _ _ _ _ Hoi Hin)).
  - assert (output_neuron nc [] (Id (Feature n')) = [false])as H.
    now rewrite (output_neuron_Output _ _ Hinn'), (is_initial_output _ Ht0 _ Hinn').
    rewrite H, map_cons, (CurPot_cons_oi _ _ _ _ _ Hoi).
    apply Qeq_plus_compat.
    * apply Nat.ltb_lt in Hid.
      rewrite Hid.
      apply Qeq_refl.
    * now rewrite (curpot_neuron_CurPot  _ _ Hin).
  - rewrite (NstepsCircuit_output_neuron _ _ _ _ Hinn'), map_cons.
    rewrite (CurPot_cons_oi _ _ _ _ _ Hoi).
    rewrite (Qeq_bool_equiv_r _ _ _ (IH _)).
    apply Qeq_plus_compat.
    * apply Nat.ltb_lt in Hid.
      rewrite Hid.
      apply Qeq_refl.
    * destruct (Tau (Feature n) <=?
              CurPot (AfterNstepsNeuron n (map (fun (i0 : bool) (x : nat) => i0)%nat
            (output_neuron nc inp (Id (Feature n')))) (length (ListNeuro nc) + SupplInput nc))).
  apply Qeq_refl.
  now apply Qeq_mul_compat_r.
Qed.  



Lemma output_neuron_nstep_oi_in_aux : forall nc i id inp n,
    is_initial nc ->
    In n (ListNeuro nc) ->
    One_Input_Or_Less (Feature n) id (length (ListNeuro nc) + SupplInput nc) ->
    (id < length (ListNeuro nc))%nat ->
    output_neuron nc (i :: inp) (Id (Feature n)) = Output (AfterNstepsNeuron n (map (fun i => (fun x => i)) (output_neuron nc inp id)) (length (ListNeuro nc) + SupplInput nc)).
Proof.
  intros nc i id inp n Ht0 Hin Hoi Hid.
  generalize Hid; intros Hidn.
  apply len_inf_in_listneuro in Hidn as [n' [Hinn' Hidn']].
  subst id.
  revert i.
  induction inp as [|i' inp IH]; intros i; rewrite (NstepsCircuit_output_neuron _ _ _ _ Hin).
  - assert (output_neuron nc [] (Id (Feature n')) = [false])as H.
    now rewrite (output_neuron_Output _ _ Hinn'), (is_initial_output _ Ht0 _ Hinn').
    rewrite H, map_cons, AfterNSN_curpot_output_unfold.
    f_equal.
    * rewrite (Qeq_bool_equiv_r _ _ _ (curpot_neuron_nstep_oi_int _ _ _ _ _ Ht0 Hin Hoi Hid)).
      now rewrite H, map_cons.
    * now rewrite (output_neuron_Output  _ _ Hin).
  - rewrite (NstepsCircuit_output_neuron _ _ _ _ Hinn'), map_cons.
    rewrite AfterNSN_curpot_output_unfold.
    f_equal; [|apply IH].
    rewrite (Qeq_bool_equiv_r _ _ _ (curpot_neuron_nstep_oi_int _ _ _ _ _ Ht0 Hin Hoi Hid)).
    now rewrite (NstepsCircuit_output_neuron _ _ _ _ Hinn'), map_cons.
Qed.  


Lemma output_neuron_nstep_oi_in : forall nc id inp n,
    is_initial nc ->
    In n (ListNeuro nc) ->
    One_Input_Or_Less (Feature n) id (length (ListNeuro nc) + SupplInput nc) ->
    (id < length (ListNeuro nc))%nat ->
    output_neuron nc inp (Id (Feature n)) = Output (AfterNstepsNeuron n (if (0 <? length inp)%nat then (map (fun i => (fun x => i)) (output_neuron nc (tl inp) id)) else []) (length (ListNeuro nc) + SupplInput nc)).
Proof.
  intros nc id inp n Hinit Hin Hoi Hid.
  destruct inp as [|i inp].
  - unfold output_neuron.
    simpl.
    now rewrite (find_neuro_in _ _ Hin).
  - now apply output_neuron_nstep_oi_in_aux.
Qed.




(** Properties on a neuron expend to the circuit **)


(* Always Positive *)

Lemma AlwaysNNegNC: forall n inp nc,
    is_initial nc ->
    In n (ListNeuro nc) ->
    (forall id, (id < length (ListNeuro nc) + SupplInput nc)%nat -> 0 <= Weights (Feature n) id) ->
    0 <= curpot_neuron nc inp (Id (Feature n)).
Proof.
  intros n inp nc Hinit Hin Hw.
  rewrite curpot_neuron_nstep; trivial.
  apply Hinit in Hin.
  now apply Always_N_Neg.  
Qed.


(* Inhibitor Effect *)

Lemma Inhibitor_Effect_NC : forall n inp nc,
    is_initial nc ->
    In n (ListNeuro nc) ->
    (forall id, (id < length (ListNeuro nc) + SupplInput nc)%nat -> Weights (Feature n) id <= 0) ->
    forall a,
      In a (output_neuron nc inp (Id (Feature n))) ->
      a = false.
Proof.
  intros n inp nc Hinit Hin Htau a.
  rewrite output_neuron_nstep; trivial.
  apply Hinit in Hin.
  now apply Inhibitor_Effect.
Qed.



(* Delayer Effect : with internal and external unique input*)

Lemma One_Input_NC_delay_Int : forall n1 n2 inp nc,
    is_initial nc ->
    In n1 (ListNeuro nc) ->
    In n2 (ListNeuro nc) ->
    One_Input_Or_Less (Feature n1) (Id (Feature n2)) (length (ListNeuro nc) + SupplInput nc) ->
    Tau (Feature n1) <= Weights (Feature n1) (Id (Feature n2)) ->
    output_neuron nc inp (Id (Feature n1)) =
      tl (output_neuron nc inp (Id (Feature n2))) ++ [false].
Proof.
  intros n1 n2 inp nc Hinit Hin1 Hin2 Hoi Htau .
  apply IdInfLen in Hin2 as Hlen2.
  apply Hinit in Hin1 as Hinit1.
  destruct (Hinit _ Hin2) as [nf2 Hinit2].
  rewrite (output_neuron_nstep_oi_in _ (Id (Feature n2))); try solve [now apply SimplS_One_Input_Or_Less_succ|trivial].
  rewrite (Delayer_Effect (Id (Feature n2))); trivial.
  case_eq (0 <? length inp)%nat; intros H.
  * f_equal.
    apply Nat.ltb_lt in H.
    apply (nth_split _ (fun _ => false)) in H as [l1 [l2 [Ha Hb]]].
    apply length_zero_iff_nil in Hb.
    subst.
    rewrite Ha.
    simpl.
    rewrite map_map, map_id.
    now rewrite NstepsCircuit_output_neuron.
  * apply Nat.ltb_ge in H.
    apply Nat.le_0_r in H.
    apply length_zero_iff_nil in H.
    subst.
    unfold output_neuron.
    simpl.
    rewrite (find_neuro_in _ _ Hin2).
    now rewrite (proj1 (proj2 Hinit2)).
Qed.


Lemma One_Input_NC_delay_Ext: forall n m inp nc,
    is_initial nc ->
    In n (ListNeuro nc) ->
    (length (ListNeuro nc) <= m)%nat ->
    (m < length (ListNeuro nc) + SupplInput nc) %nat ->
    One_Input_Or_Less (Feature n) m (length (ListNeuro nc) + SupplInput nc) ->
    Tau (Feature n) <= Weights (Feature n) m ->
    output_neuron nc inp (Id (Feature n)) =
      map (fun f => f m) inp ++ [false].
Proof.
  intros n m inp nc Hinit Hin Hm1 Hm2 Hoi Htau.
  apply Hinit in Hin as Hinit'.
  rewrite (output_neuron_nstep_oi_ext _ m _ _ Hin); trivial.
  now apply (Delayer_Effect m).
Qed.



(* Filtering Effect *)


Lemma One_Input_NC_Filtering_Effect : forall n m inp nc,
    is_initial nc ->
    In n (ListNeuro nc) ->
    (m < length (ListNeuro nc) + SupplInput nc) %nat ->
    One_Input_Or_Less (Feature n) m (length (ListNeuro nc) + SupplInput nc) ->
    Weights (Feature n) m < Tau (Feature n) ->
    forall a1 a2 l1 l2,
      output_neuron nc inp (Id (Feature n)) = l1 ++ a1 :: a2 :: l2 -> a1 && a2 = false.
Proof.
  intros n m inp nc Hinit Hin Hm2 Hoi Htau.
  apply Hinit in Hin as Hinit'.
  case_eq (m <? length (ListNeuro nc))%nat; intros Hm.
  - apply Nat.ltb_lt in Hm.
    rewrite (output_neuron_nstep_oi_in _ m inp _ Hinit Hin Hoi); trivial.
    now apply (Filtering_Effect m).
  - apply Nat.ltb_ge in Hm; rewrite (output_neuron_nstep_oi_ext _ m inp _ Hin Hoi); trivial.
    now apply (Filtering_Effect m).
Qed.


(* Spike Decrease : with internal and external unique input*)


Lemma One_Input_NC_Spike_Decreasing_Int : forall n1 n2 inp nc,
    is_initial nc ->
    In n1 (ListNeuro nc) ->
    In n2 (ListNeuro nc) ->
    One_Input_Or_Less (Feature n1) (Id (Feature n2)) (length (ListNeuro nc) + SupplInput nc) ->
    (count_occ bool_dec (output_neuron nc inp (Id (Feature n1))) true <= count_occ bool_dec (output_neuron nc (tl inp) (Id (Feature n2))) true)%nat.
Proof.
  intros n1 n2 inp nc Hinit Hin1 Hin2 Hoi.
  apply Hinit in Hin1 as Hinit'.
  apply IdInfLen in Hin2 as Hlen2.
  rewrite (output_neuron_nstep_oi_in _ (Id (Feature n2))); try solve [now apply SimplS_One_Input_Or_Less_succ|trivial].
  case_eq (0 <? length inp)%nat; intros Hlen.
  * assert (H := Spike_Decreasing _ (map (fun (x : bool) (_ : nat) => x) (output_neuron nc (tl inp) (Id (Feature n2)))) _ _ Hoi Hinit').
    now rewrite map_map, map_id in H.
  * simpl.
    destruct Hinit' as [nf [_ [Hinit' _]]].
    rewrite Hinit'.
    apply Nat.le_0_l.
Qed.


Lemma One_Input_NC_Spike_Decreasing_Ext: forall n m inp nc,
    is_initial nc ->
    In n (ListNeuro nc) ->
    (length (ListNeuro nc) <= m)%nat ->
    (m < length (ListNeuro nc) + SupplInput nc) %nat ->
    One_Input_Or_Less (Feature n) m (length (ListNeuro nc) + SupplInput nc) ->
    (count_occ bool_dec (output_neuron nc inp (Id (Feature n))) true <= count_occ bool_dec (map (fun f => f m) inp) true)%nat.
Proof.
  intros n m inp nc Hinit Hin Hm1 Hm2 Hoi.
  apply Hinit in Hin as Hinit'.
  rewrite (output_neuron_nstep_oi_ext _ m _ _ Hin); trivial.
  now apply (Spike_Decreasing m).
Qed.
