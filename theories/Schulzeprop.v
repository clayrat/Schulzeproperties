(*
Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.ZArith.ZArith.*)
Require Import Lia.

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype fintype ssrint order bigop path.
From Schulze Require Import ListLemma.
(*
Require Import Psatz.
Import ListNotations.
Open Scope int.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.
*)

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.
Open Scope ring_scope.

Section Properties.

  Variable cand : finType.
  Hypothesis cand_nonempty : 0 < #|{ : cand}|.


  Section Evote.
    (** Section 2: Specification of Schulze Vote Counting **)

    (* marg is the margin in Schulze counting, i.e. marg c d is the number of
       voters that perfer c over d. The existence of the margin function
       is assumed for the specification of Schulze Voting and will be
       constructed from incoming ballots later *)
    Variable marg : cand -> cand -> int.


    (* prop-level path *)
    Inductive Path (k: int) : cand -> cand -> Prop :=
    | unit c d   : k <= marg c d ->               Path k c d
    | cons c d e : k <= marg c d -> Path k d e -> Path k c e.

    (* winning condition of Schulze Voting *)
    Definition wins_prop (c: cand) :=
      forall d: cand, exists k: int,
        Path k c d /\ (forall l, Path l d c -> l <= k).

    (* dually, the notion of not winning: *)
    Definition loses_prop (c : cand) :=
      exists (k: int) (d: cand),
        Path k d c /\ (forall l, Path l c d -> l < k).

    (** Section 3: A Scrutiny Sheet for the Schulze Method **)

    (* boolean function that determines whether the margin between a
       pair  of candidates is below a given integer *)
    Definition marg_lt (k : int) (p : (cand * cand)) :=
      marg p.1 p.2 < k.

    (* definition of the (monotone) operator W_k that defines coclosed sets *)
    Definition W (k : int) (p : pred (cand * cand)) (x : cand * cand) :=
        (marg_lt k x) &&
        (all (fun m => (marg_lt k (x.1, m)) || (p (m, x.2))) (enum {:cand})).

    (* k-coclosed predicates *)
    Definition coclosed (k : int) (p : pred (cand * cand)) :=
      forall x, p x -> W k p x.

      (* TODO this should be smth like *)
      (* {xs : seq cand | path (fun x y => k <= marg x y) c xs && belast c xs == d} *)
      (* i.e. at runtime it's just a list of (intermediate) candidates *)
(*
    (* type-level path to replace prop-level path *)
    Inductive PathT (k: int) : cand -> cand -> Type :=
    | unitT c d : marg c d >= k -> PathT k c d
    | consT c d e : marg c d >= k -> PathT k d e -> PathT k c e.

    (* type-level winning condition in Schulze counting *)
    Definition wins_type c :=
      forall d : cand, existsT (k : int),
      ((PathT k c d) *
       (existsT (f : (cand * cand) -> bool), f (d, c) = true /\ coclosed (k + 1) f))%type.

    (* dually, the type-level condition for non-winners *)
    Definition loses_type (c : cand) :=
      existsT (k : int) (d : cand),
      ((PathT k d c) *
       (existsT (f : (cand * cand) -> bool), f (c, d) = true /\ coclosed k f))%type.

    (* type-level notions of winning and losing are equivalent *)
    (* auxilary lemmas needed for the proof of equivalence     *)
    (* search for wins_prop_type and wins_type_prop for the    *)
    (* statement and proof of equivalence, dually for losing.  *)

    (* type-level paths allow to construct evidence for the existence of paths *)
    Lemma path_equivalence : forall c d k , PathT k c d -> Path k c d.
    Proof.
      refine
        (fix F c d k H {struct H}:=
           match H with
           | unitT _ cf df mrg => unit _ cf df mrg
           | consT _ cf df ef mrg t => cons _ cf df ef mrg (F _ _ _ t)
           end).
    Qed.
*)


    (* mp stands for midpoint and the lemma below shows that for a pair of candidates (a, c)
       with x = (a, c) in W_k p, and a putative midpoint b, we have that marg a b < k or p b c. *)
    Lemma mp_log (k : int) (x : cand * cand) (p : pred (cand * cand)) :
        all (fun m => (marg_lt k (x.1, m)) || (p (m, x.2))) (enum {:cand}) ->
        forall b, p (b, x.2) || (marg x.1 b < k).
    Proof.
    move=>H b.
    move/allP: H=>/(_ b); rewrite mem_enum =>/(_ erefl).
    by rewrite orbC.
    Qed.

    (* all elements (x, y) in a k-coclosed set can only be joined by a path of strength < k *)
    Lemma coclosed_path k f :
      coclosed k f ->
      forall s x y, Path s x y -> f (x, y) -> s < k.
    Proof.
    move=>Hcc s x y; elim=>[c d| c d e] H.
    - case/Hcc/andP=>/= Hl _.
      by apply: (le_lt_trans H).
     move=>Hp IH /[dup] Hf /Hcc; case/andP=>Hl /mp_log /= /(_ d); case/orP=>// Hm.
     by apply/le_lt_trans/Hm.
    Qed.

    Lemma coclosed_path_bound k1 k2 f :
      k1 < k2 -> coclosed k1 f -> coclosed k2 f.
    Proof.
    move=>Hk Hf [c d] Hfx.
    move: Hf => /(_ _ Hfx); case/andP=>H1 H2.
    apply/andP; split; first by apply/lt_trans/Hk.
    apply/sub_all/H2=>z /=; case/orP=>[Hm|->]; last by rewrite orbT.
    by rewrite /marg_lt (lt_trans Hm Hk).
    Qed.

    Definition listify (m : cand -> cand -> int) : seq (cand * cand * int) :=
      map (fun s => (s.1, s.2, m s.1 s.2)) (all_pairs (enum {:cand})).

    Lemma in_pairs a b :
      (a, b) \in all_pairs (enum {:cand}).
    Proof. by apply: all_pairsin; rewrite mem_enum. Qed.

    Fixpoint linear_search (c d : cand) l :=
      if l is (c1, c2, k) :: t then
        if (c == c1) && (d == c2) then k else linear_search c d t
      else marg c d.

    Theorem equivalent_m c d m : linear_search c d (listify m) = m c d.
    Proof.
    rewrite /listify.
    move: (in_pairs c d); elim: (all_pairs (enum cand))=>// [[a1 a2]] l IH /=.
    rewrite inE; case/orP.
    - by case/eqP=>->->; rewrite !eq_refl.
    by move/IH=>->; case: ifP=>//; case/andP=>/eqP->/eqP->.
    Qed.


    Fixpoint M_old (n : nat) (c d : cand) : int :=
      match n with
      | 0%nat => marg c d
      | S n' =>
        Order.max (M_old n' c d) (maxlist (map (fun x : cand => Order.min (marg c x) (M_old n' x d)) (enum cand)))
      end.

    (* M is the iterated margin function and maps a pair of candidates c, d to the
       strength of the strongest path of length at most (n + 1) *)

    Fixpoint MM n :=
      match n with
      | O => listify marg
      | S n' =>
        let uu := MM n' in
        listify (fun c d =>
                   let u := linear_search c d uu in
                   let t := maxlist
                              (map (fun x => Order.min (marg c x) (linear_search x d uu)) (enum cand)) in
                   Order.max u t)
      end.

    Definition M n : cand -> cand -> int :=
      let l := MM n in
      fun c d => linear_search c d l.


    Lemma M_M_new_equal n c d : M n c d = M_old n c d.
    Proof.
      induction n. unfold M. simpl. intros c d. rewrite equivalent_m. auto.
      intros c d.  unfold M in *. simpl. rewrite equivalent_m.
      assert (Ht: maxlist (map (fun x : cand => int.min (marg c x) (linear_search x d (MM n))) cand_all) =
                  maxlist (map (fun x : cand => int.min (marg c x) (M_old n x d)) cand_all)).
      apply f_equal.
      clear cand_not_nil. clear cand_fin.
      induction cand_all. auto. simpl. pose proof (IHn a d).
      rewrite H. apply f_equal. auto.
      rewrite Ht. rewrite IHn. auto.
    Qed.


    (* partial correctness of iterated margin function: if the strength M n c d
       of the strongest path of length <= n+1 between c and d is at least s, then
       c and d can be joined by a type-level path of this strength *)
    Theorem iterated_marg_patht : forall n s c d, M n c d >= s -> PathT s c d.
    Proof.
      induction n.
      intros s c d H. constructor. unfold M in *. simpl in *. rewrite equivalent_m in H. auto.
      intros s c d H. unfold M in *. simpl in H. rewrite equivalent_m in H.
      unfold int.max in H.
      destruct (linear_search c d (MM n)
                              ?= maxlist (map (fun x : cand => int.min (marg c x) (linear_search x d (MM n))) cand_all)).
      apply IHn. auto.
      apply max_of_nonempty_list_type in H. destruct H as [x [H1 H2]].
      apply z_min_lb in H2. destruct H2.
      specialize (IHn _ _ _ H0). specialize (consT _ _ _ _ H IHn); auto.
      apply cand_not_nil.  apply dec_cand. apply IHn. assumption.
    Defined.


    (* as type level paths induce prop-level paths, the same as above also holds for prop-level
       paths *)
    Lemma iterated_marg_path : forall (n : nat) (s : int) (c d : cand),
        M n c d >= s -> Path s c d.
    Proof.
      intros n s c d Hm.
      apply path_equivalence. apply iterated_marg_patht with (n := n).
      assumption.
    Qed.

    (* existence of a a path between c and d of strength s gives an interate of the
       iterated margin function with value at least s *)
    Lemma path_iterated_marg : forall (s : int) (c d : cand),
        Path s c d -> exists n, M n c d >= s.
    Proof.
      intros s c d H.  induction H.
      exists 0%nat. unfold M. simpl. rewrite equivalent_m. auto. destruct IHPath.
      exists (S x). unfold M in *. simpl.  rewrite equivalent_m. apply z_max_lb. right.
      apply max_of_nonempty_list.
      apply cand_not_nil. apply dec_cand. exists d.
      split. pose proof (cand_fin d). auto.
      apply z_min_lb. split. auto. auto.
    Qed.

    (* monotonicity of the iterated margin function *)
    Lemma monotone_M : forall (n m : nat) c d, (n <= m)%nat  -> M n c d <= M m c d.
    Proof.
      intros n m c d H.  induction H; simpl; try lia.
      apply int.ge_le. unfold M at 1. simpl. rewrite equivalent_m.
      apply z_max_lb with (m := M m c d).
      left. lia.
    Qed.

    (* Here, we view paths as lists of candidates, and str computes the strength of
       a path relative to the given margin function *)
    Fixpoint str c l d :=
      match l with
      | [] => marg c d
      | (x :: xs) => int.min (marg c x)  (str x xs d)
      end.

    (* the iterated margin function is correct relative to the length of a path *)
    Lemma path_len_iterated_marg : forall k c d s l,
        (length l <= k)%nat -> str c l d >= s -> M k c d >= s.
    Proof.
      induction k. intros. assert ((length l <= 0)%nat -> l = []).
      { destruct l. intros. reflexivity.
        simpl in *. inversion H. }
      specialize (H1 H). subst. simpl in *. unfold M in *. simpl. rewrite equivalent_m. auto.
      intros. simpl in *. destruct l. simpl in *.
      unfold M in *. simpl.

      rewrite equivalent_m. apply z_max_lb.
      left. apply IHk with []. simpl. lia. simpl. auto.
      simpl in *. apply z_min_lb in H0. destruct H0.
      unfold M in *.  simpl.
      rewrite equivalent_m.
      apply z_max_lb. right. apply max_of_nonempty_list.
      apply cand_not_nil. apply dec_cand. exists c0. split. specialize (cand_fin c0). trivial.
      apply z_min_lb. split.
      lia. apply IHk with l. lia. lia.
    Qed.

    (* characterisation of the iterated margin function in terms of paths *)
    Lemma iterated_marg_char: forall k c d s,
        M k c d >= s <-> exists (l : list cand), (length l <= k)%nat /\ str c l d >= s.
    Proof.
      split. generalize dependent s. generalize dependent d.
      generalize dependent c. induction k. simpl. intros. exists []. simpl. intuition.
      unfold M in *. simpl in H. rewrite equivalent_m in H. auto.

      simpl. intros. unfold M in *. simpl in H.

      rewrite equivalent_m in H.  pose proof (proj1 (z_max_lb (M k c d) _ s) H).
      destruct H0.
      specialize (IHk c d s H0). destruct IHk as [l [H1 H2]]. exists l. lia. clear H.
      pose proof
           (max_of_nonempty_list _ cand_all cand_not_nil dec_cand s
                                 (fun x : cand => int.min (marg c x) (M k x d))).
      destruct H. clear H1. specialize (H H0). destruct H as [e [H1 H2]].
      pose proof (proj1 (z_min_lb _ _ s) H2). destruct H.
      specialize (IHk e d s H3). destruct IHk as [l [H4 H5]].
      exists (e :: l). simpl. split. lia.
      apply z_min_lb. intuition.
      (* otherway *)
      intros. destruct H as [l [H1 H2]].
      pose proof (path_len_iterated_marg k c d s l H1 H2). lia.
    Qed.

    (* every path of strength >= s can be split into two paths of strength >= s *)
    Lemma path_split: forall c d a l1 l2 s,
        str c (l1 ++ a :: l2) d >= s <-> str c l1 a >= s /\ str a l2 d >= s.
    Proof.
      split. generalize dependent s. generalize dependent l2.
      generalize dependent a. generalize dependent d. generalize dependent c.
      induction l1; simpl; intros.
      apply z_min_lb in H. auto. apply z_min_lb in H. destruct H.
      assert ((marg c a) >= s /\ (str a l1 a0) >= s /\ str a0 l2 d >= s ->
              int.min (marg c a) (str a l1 a0) >= s /\ str a0 l2 d >= s).
      { intros. destruct H1 as [H1 [H2 H3]]. split. apply z_min_lb. auto. auto. }
      apply H1. split. assumption. apply IHl1. assumption.
      (* other part *)
      generalize dependent s. generalize dependent l2.
      generalize dependent a. generalize dependent d. generalize dependent c.
      induction l1; simpl; intros. apply z_min_lb. auto.
      apply z_min_lb. destruct H. apply z_min_lb in H. destruct H.
      split. auto. apply IHl1. auto.
    Qed.

    (* cutting out a loop from a path does not decrease its strength *)
    Lemma path_cut: forall c d a l l1 l2 l3 s,
        l = l1 ++ a :: l2 ++ a :: l3 -> str c l d >= s -> str c (l1 ++ a :: l3) d >= s.
    Proof.
      intros. subst. apply path_split in H0. destruct H0.
      apply path_split in H0. destruct H0.
      pose proof (proj2 (path_split c d a l1 l3 s) (conj H H1)). auto.
    Qed.

    (* the iterated margin function stabilizes after n iterations, where n is the
       number of candidates. *)
    Lemma iterated_marg_stabilises: forall k n c d (Hn: (length cand_all = n)%nat),
        M (k + n) c d <= M n  c d.
    Proof.
      induction k using (well_founded_induction lt_wf).
      intros n c d Hn.
      remember (M (k + n) c d) as s.
      pose proof (int.eq_le_incl _ _ Heqs).
      apply int.le_ge in H0.
      pose proof (proj1 (iterated_marg_char _ _ _ _) H0).
      destruct H1 as [l [H1 H2]].
      (* number of candidates <= length Evote.cand_all \/ > length Evote.cand_all *)
      assert ((length l <= n)%nat \/ (length l > n)%nat) by lia.
      destruct H3 as [H3 | H3].
      pose proof (proj2 (iterated_marg_char n c d s)
                        (ex_intro (fun l => (length l <= n)%nat /\ str c l d >= s) l (conj H3 H2))).
      lia.
      (* length l > length Evote.cand_all and there are candidates. Remove the duplicate
         candidate *)
      rewrite <- Hn in H3.
      assert (covers cand cand_all l).
      { unfold covers. intros. pose proof (cand_fin x). assumption. }
      pose proof (list_split_dup_elem _ n cand_all dec_cand Hn l H3 H4).
      destruct H5 as [a [l1 [l2 [l3 H5]]]].
      pose proof (path_cut  _ _ _ _ _ _ _ _ H5 H2).
      remember (l1 ++ a :: l3) as l0.
      assert ((length l0 <= n)%nat \/ (length l0 > n)%nat) by lia.
      destruct H7.
      pose proof (iterated_marg_char n c d s). destruct H8.
      assert ((exists l : list cand, (length l <= n)%nat /\ str c l d >= s)).
      exists l0. intuition. specialize (H9 H10).  lia.
      rewrite Hn in H3.
      specialize (list_and_num _ _ _ H3); intros. destruct H8 as [p H8].
      specialize (list_and_num _ _ _ H7); intros. destruct H9 as [k' H9].
      assert ((length l0 < length l)%nat).
      { rewrite Heql0, H5.
        rewrite app_length. rewrite app_length.
        simpl. rewrite app_length. simpl.
        lia. }
      rewrite H9 in H10. rewrite H8 in H10.
      assert (((k' + n) < (p + n))%nat -> (k' < p)%nat) by lia.
      specialize (H11 H10). assert (k' < k)%nat by lia.
      specialize (H k' H12 n c d Hn).
      pose proof (iterated_marg_char (length l0) c d (str c l0 d)).
      destruct H13.
      assert ((exists l : list cand, (length l <= length l0)%nat /\ str c l d >= str c l0 d)).
      { exists l0. lia. }
      specialize (H14 H15). clear H13. rewrite <- H9 in H.
      lia.
    Qed.

    (* the iterated margin function reaches a fixpoint after n iterations, where
       n is the number of candidates *)
    Lemma iterated_marg_fp : forall (c d : cand) (n : nat),
        M n c d <= M (length cand_all) c d.
    Proof.
      intros c d n. assert ((n <= (length cand_all))%nat \/
                            (n >= (length cand_all))%nat) by lia.
      destruct H. apply monotone_M. assumption.
      remember ((length cand_all)) as v.
      assert ((n >= v)%nat -> exists p, (n = p + v)%nat).
      { intros. induction H. exists 0%nat. lia.
        assert ((v <= m)%nat -> (m >= v)%nat) by lia.
        specialize (H1 H). specialize (IHle H1). destruct IHle as [p H2].
        exists (S p). lia. }
      specialize (H0 H). destruct H0 as [p H0].
      subst. apply  iterated_marg_stabilises. auto.
    Qed.

    (* boolean valued function that determines election winners based on the
       (fixpoint of the) iterated margin function *)
    Definition c_wins c :=
      forallb (fun d => (M (length cand_all) d c) <=? (M (length cand_all) c d))
              cand_all.
    (* characterisation of c_wins returning true in terms of iterated margin function *)
    Lemma c_wins_true (c : cand) :
      c_wins c = true <-> forall d, M (length cand_all) d c <= M (length cand_all) c d.
    Proof.
      split; intros.
      unfold c_wins in H.
      pose proof
           (proj1 (forallb_forall
                     (fun d : cand => M (length cand_all) d c <=?
                                      M (length cand_all) c d) cand_all) H).
      pose proof (H0 d (cand_fin d)). simpl in H1.
      apply Zle_bool_imp_le. assumption.
      unfold c_wins. apply forallb_forall. intros x Hin.
      pose proof H x. apply Zle_imp_le_bool. assumption.
    Qed.

    (* characterisation of c_wins returning false in terms of the interated margin function *)
    Lemma c_wins_false (c : cand):
      c_wins c = false <-> exists d, M (length cand_all) c d < M (length cand_all) d c.
    Proof.
      split; intros. unfold c_wins in H.
      apply forallb_false in H. destruct H as [x [H1 H2]].
      exists x. apply int.leb_gt in H2. lia.
      destruct H as [d H]. unfold c_wins. apply forallb_false.
      exists d. split. pose proof (cand_fin d). assumption.
      apply int.leb_gt. lia.
    Qed.


    (* the propositional winning condition implies winning in terms of the interated margin
       function *)
    Lemma wins_prop_iterated_marg (c : cand): wins_prop c ->
                                              forall d, M (length cand_all) d c <= M (length cand_all) c d.
    Proof.
      intros. specialize (H d). destruct H as [k [H1 H2]].
      remember (M (length cand_all) d c) as s.
      apply int.eq_le_incl in Heqs.
      apply int.le_ge in Heqs.
      pose proof (iterated_marg_path _ _ _ _ Heqs). specialize (H2 s H).
      apply  path_iterated_marg in H1. destruct H1 as [n H1].
      pose proof (iterated_marg_fp c d n). lia.
    Qed.

    (* winning in terms of the iterated margin function gives the type-level winning condition *)
    Lemma iterated_marg_wins_type (c : cand): (forall d,
                                                  M (length cand_all) d c <= M (length cand_all) c d) ->
                                              wins_type c.
    Proof.
      (* rewrite it using refine tactic *)

      intros H d. specialize (H d).
      remember (M (length cand_all) c d) as s eqn:Heqs.
      apply int.eq_le_incl in Heqs.
      apply int.le_ge in Heqs. exists s.
      pose proof (iterated_marg_patht _ _ _ _ Heqs) as Hi.
      split.
      - intuition.
      - remember (M (length cand_all) d c) as r eqn:Heqr.
        exists (fun x => M (length cand_all) (fst x) (snd x) <=? r).
        split.
        + apply int.leb_le. simpl. intuition.
        + intros x Hx. destruct x as (x, z).
          apply int.leb_le in Hx. apply andb_true_iff.
          split.
          * apply int.ltb_lt. simpl in *.
            clear Heqs. clear Heqr.
            induction (length cand_all); simpl in Hx. unfold M in Hx. simpl in Hx.
            rewrite equivalent_m in Hx.
            intuition.
            apply IHn. unfold M in Hx. simpl in Hx.
            rewrite equivalent_m in Hx.  apply int.max_lub_iff in Hx. intuition.
          * apply forallb_forall. intros y Hy. apply orb_true_iff.
            simpl in *.
            assert (A : marg x y <= s \/ marg x y > s) by lia.
            destruct A as [A1 | A2].
            left. apply int.ltb_lt. simpl. lia.
            right. apply int.leb_le.
            assert (B : M (length cand_all) y z <= r \/ M (length cand_all) y z >= r + 1) by lia.
            destruct B as [B1 | B2].
            intuition.
            apply iterated_marg_path in B2.
            assert (A3 : marg x y >= r + 1) by lia.
            pose proof (cons _ _ _ _ A3 B2) as C.
            apply  path_iterated_marg in C. destruct C as [n C].
            pose proof (iterated_marg_fp x z n). lia.
    Defined.



    (* the type level winning condition can be reconstruced from *)
    (* propositional knowledge of winning *)
    Lemma wins_prop_type : forall c, wins_prop c -> wins_type c.
    Proof.
      intros c H. unfold wins_prop, wins_type in *.
      apply iterated_marg_wins_type. apply wins_prop_iterated_marg. auto.
    Qed.

    (* dually, the type-level information witnessing winners *)
    (* entails prop-level knowledge. *)
    Lemma wins_type_prop : forall c, wins_type c -> wins_prop c.
    Proof.
      intros c H. unfold wins_prop, wins_type in *. intros d.
      destruct (H d) as [k [H1 [f [H3 H4]]]].
      exists k. split. apply path_equivalence. auto.
      intros l H5. pose proof (coclosed_path _ _ H4).
      pose proof (H0 l _ _ H5 H3). lia.
    Qed.

    (* the losing condition in terms of the iterated margin function *)
    Lemma loses_prop_iterated_marg (c : cand):
      loses_prop c ->
      (exists d, M (length cand_all) c d < M (length cand_all) d c).
    Proof.
      intros. destruct H as [k [d [H1 H2]]].
      exists d. remember (M (length cand_all) c d)  as s.
      pose proof (int.eq_le_incl _ _ Heqs) as H3.
      apply int.le_ge in H3. apply iterated_marg_path in H3. specialize (H2 s H3).
      apply  path_iterated_marg in H1. destruct H1 as [n H1].
      pose proof (iterated_marg_fp d c n). lia.
    Qed.

    (* existential quantifiers over finite lists can be reified into Sigma-types for
       decidable properties *)
    Definition exists_fin_reify {A: Type} (P: A -> Prop):
      (forall a: A, {P a} + {~(P a)}) ->
      forall l: list A, (exists a, In a l /\ P a) -> existsT a, P a :=
      fun Pdec =>
        fix F l {struct l} :=
        match l  as m return ((exists a : A, In a m /\ P a) -> existsT a : A, P a) with
        | [] =>
          fun H : exists a : A, In a [] /\ P a =>
            (fun Hf : False => (fun X : existsT a : A,P a => X)
                                 match Hf return
                                       (existsT a : A,P a) with end)
              match H with
              | ex_intro _ a (conj Ha _) => (fun H1 : False => H1) match Ha return False with end
              end
        | h :: t => fun H =>
                      match (Pdec h) with
                      | left e => existT _ h e
                      | right r =>
                        F t
                          match H with
                          | ex_intro _ a (conj (or_introl e) Hpa) =>
                            (fun rr : ~ P a => False_ind (exists a1 : A, In a1 t /\ P a1) (rr Hpa))
                              (eq_ind h (fun hh : A => ~ P hh) r a e)
                          | ex_intro _ a (conj (or_intror rr as Hin) Hpa as a0) =>
                            ex_intro _ a (conj rr Hpa)
                          end
                      end
        end.

    (* reification of candidates given propositional existence *)
    Corollary reify_opponent (c: cand):
      (exists  d, M  (length cand_all) c d < M (length cand_all) d c) ->
      (existsT d, M  (length cand_all) c d < M (length cand_all) d c).
      refine (fun Hex  =>
                (fun Hdec : forall d : cand,
                     {M (length cand_all) c d < M (length cand_all) d c} +
                     {~ M (length cand_all) c d < M (length cand_all) d c} =>
                   exists_fin_reify
                     _  Hdec cand_all
                     match Hex with
                     | ex_intro _ d Hex0 =>
                       ex_intro _ d (conj (cand_fin d) Hex0)
                     end)
                  (fun d : cand =>
                     let s := Z_lt_ge_bool (M (length cand_all) c d) (M (length cand_all) d c) in
                     let (b, P) := s in
                     (if b as bt
                         return
                         ((if bt
                           then M (length cand_all) c d < M (length cand_all) d c
                           else M (length cand_all) c d >= M (length cand_all) d c) ->
                          {M (length cand_all) c d < M (length cand_all) d c} +
                          {~ M (length cand_all) c d < M (length cand_all) d c})
                      then fun Pt => left Pt
                      else fun Pf => right (fun H => Pf H)) P)).
    Defined.



    (* reconstructon of the losing condition type-level losing from interated
       margin function *)
    Lemma iterated_marg_loses_type (c : cand) :
      (exists d, M (length cand_all) c d < M (length cand_all) d c) -> loses_type c.
    Proof.
      unfold loses_type. intros.
      assert (HE:  existsT d, M  (length cand_all) c d < M (length cand_all) d c).
      apply reify_opponent. assumption.
      destruct HE as [d HE].
      remember (M (length cand_all) d c) as s. exists s, d.
      split. assert (H1 : M (length cand_all) d c >= s) by lia.
      apply iterated_marg_patht in H1. auto.
      exists (fun x => M (length cand_all) (fst x) (snd x) <? s).
      simpl in *. split. apply int.ltb_lt. lia.
      unfold coclosed. intros x; destruct x as (x, z); simpl in *.
      intros. apply int.ltb_lt in H0. unfold W.
      apply andb_true_iff. split. unfold marg_lt. simpl. apply int.ltb_lt.
      clear H. clear Heqs.
      induction (length cand_all). unfold M in *. simpl in *.  rewrite equivalent_m in H0.  lia.
      unfold M in H0.
      simpl in H0. rewrite equivalent_m in H0.
      apply int.max_lub_lt_iff in H0. destruct H0. apply IHn. auto.
      unfold M in HE.
      simpl in HE. rewrite equivalent_m in HE.
      apply int.max_lub_lt_iff in HE. destruct HE as [H1 H2]. assumption. assumption.

      apply forallb_forall. intros y Hy.
      apply orb_true_iff. unfold marg_lt. simpl.
      assert (marg x y < s \/ marg x y >= s) by lia.
      destruct H1. left. apply int.ltb_lt. auto.
      right. apply int.ltb_lt.
      assert (M (length cand_all) y z < s \/ M (length cand_all) y z >= s) by lia.
      destruct H2. auto.
      apply iterated_marg_path in H2.  pose proof (Evote.cons _ _ _ _ H1 H2).
      apply  path_iterated_marg in H3. destruct H3 as [n H3].
      pose proof (iterated_marg_fp x z n). lia.
    Defined.

    (* prop-level losing implies type-level losing *)
    Lemma loses_prop_type : forall c, loses_prop c -> loses_type c.
    Proof.
      intros c H. unfold loses_prop, loses_type in *. apply iterated_marg_loses_type.
      apply loses_prop_iterated_marg. auto.
    Qed.

    (* type-level losing implies prop-level losing *)
    Lemma loses_type_prop : forall c, loses_type c -> loses_prop c.
    Proof.
      intros c H. unfold loses_prop, loses_type in *.
      destruct H as [k [d [Hp [f [Hf Hc]]]]].
      exists k, d. split. apply path_equivalence. auto.
      intros l H. pose proof (coclosed_path k f Hc).
      pose proof (H0 l _ _ H Hf). lia.
    Qed.

    (* decidability of type-level winning *)
    Lemma wins_loses_type_dec : forall c, (wins_type c) + (loses_type c).
    Proof.
      intros c. destruct (c_wins c) eqn : c_wins_val.  left.
      unfold wins_type. apply  iterated_marg_wins_type. apply wins_prop_iterated_marg. intros d.
      pose proof (proj1 (forallb_forall _ cand_all) c_wins_val d (cand_fin d)).
      simpl in H. apply Zle_bool_imp_le in H. apply int.le_ge in H.
      remember (M (length cand_all) d c) as s. apply iterated_marg_path in H.
      exists s. split. assumption.
      intros. rewrite Heqs. apply  path_iterated_marg in H0. destruct H0 as [n H0].
      apply int.ge_le in H0. pose proof (iterated_marg_fp d c n). lia.
      right. apply iterated_marg_loses_type. unfold c_wins in c_wins_val.
      apply forallb_false_type in c_wins_val.
      destruct c_wins_val as [d [H1 H2]]. apply int.leb_gt in H2. exists d. auto.
    Defined.

    (* aligning c_wins with type level evidence *)
    Lemma c_wins_true_type:
      forall c : cand, c_wins c = true <-> (exists x : wins_type c, wins_loses_type_dec c = inl x).
    Proof.
      split; intros. destruct (wins_loses_type_dec c) eqn:Ht. exists w. auto.
      pose proof (loses_type_prop c l). unfold loses_prop in H0.
      apply loses_prop_iterated_marg  in H0.
      pose proof (proj1 (c_wins_true c) H). destruct H0. specialize (H1 x). lia.
      destruct H. pose proof (wins_type_prop c x). unfold wins_prop in H0.
      apply c_wins_true. apply wins_prop_iterated_marg. auto.
    Qed.

    (* aligning of c_wins with losing condition *)
    Lemma c_wins_false_type:
      forall c : cand, c_wins c = false <-> (exists x : loses_type c, wins_loses_type_dec c = inr x).
    Proof.
      split; intros. destruct (wins_loses_type_dec c) eqn:Ht.
      pose proof (wins_type_prop c w).
      pose proof (proj1 (c_wins_false c) H). unfold wins_prop in H0.
      pose proof (wins_prop_iterated_marg c H0). destruct H1. specialize (H2 x). lia.
      exists l. auto.
      destruct H. pose proof (loses_type_prop c x). unfold loses_prop in H0.
      apply c_wins_false. apply loses_prop_iterated_marg. auto.
    Qed.



  End Evote.

  (* Start of properties. Move it other module *)
  Section Propt.

    Hypothesis marg_neq :
      forall (c d : cand) (marg : cand -> cand -> int), marg c d = -marg d c.

    Lemma marg_dec : forall (a b : int), {a <= b} + {b <= a}.
    Proof.
      intros a b.
      destruct (Ztrichotomy_inf a b) as [[H1 | H2] | H3].
      left; lia.
      left; lia.
      right; lia.
    Qed.



    Definition condercet_winner (c : cand) (marg : cand -> cand -> int) :=
      forall d, marg c d >= 0.

    Lemma gen_marg_gt0 :
      forall c d n marg, condercet_winner c marg -> M marg n c d >= 0.
    Proof.
      unfold condercet_winner.
      intros c d n marg Hc.
      rewrite M_M_new_equal.
      revert d; revert n.
      induction n; cbn; try auto.
      intros d. pose proof (IHn d).
      lia.
    Qed.

    Lemma gen_marg_lt0 :
      forall c d n marg , condercet_winner c marg -> M marg n d c <= 0.
    Proof.
      unfold condercet_winner.
      intros c d n marg Hc.
      rewrite M_M_new_equal.
      revert d; revert n.
      induction n.
      + cbn. intros d. pose proof (marg_neq c d marg).
        pose proof (Hc d). lia.
      + cbn. intros d.
        apply int.max_lub_iff.
        split.
        pose proof (IHn d). lia.
        apply upperbound_of_nonempty_list; try auto.
        intros x Hx. pose proof (IHn x).
        lia.
    Qed.


    Lemma condercet_winner_genmarg :
      forall c d n marg, condercet_winner c marg -> M marg n d c <= M marg n c d.
    Proof.
      intros c d n marg Hc.
      pose proof (gen_marg_gt0 c d n marg Hc).
      pose proof (gen_marg_lt0 c d n marg Hc).
      lia.
    Qed.


    Lemma condercet_winner_headoff :
      forall c marg, condercet_winner c marg <-> (forall d,  marg d c <= marg c d).
    Proof.
      split; intros Hc d.
      unfold condercet_winner in Hc.
      pose proof (Hc d).
      pose proof (marg_neq c d marg).
      lia.

      pose proof (Hc d).
      pose proof (marg_neq d c marg).
      lia.
    Qed.



    (* if candidate c beats everyone in head to head count, then it beats
       everyone in generalized margin *)
    Lemma condercet_winner_marg (c : cand) (marg : cand -> cand -> int) :
      forall n, (forall d, marg d c <= marg c d) -> forall d, M marg n d c <= M marg n c d.
    Proof.
      intros n Hc d.
      apply condercet_winner_genmarg.
      apply condercet_winner_headoff.
      auto.
    Qed.

    (* if candidate c is condercet winner then it's winner of election *)
    Lemma condercet_winner_implies_winner (c : cand) (marg : cand -> cand -> int) :
      condercet_winner c marg -> c_wins marg c = true.
    Proof.
      intros Hc.
      pose proof  condercet_winner_genmarg.
      pose proof c_wins_true.
      apply H0. intros d.
      pose proof (H c d (length cand_all) marg Hc).
      auto.
    Qed.

    (* End of condercet property *)







    (* Beginning of reversal symmetry *)
    (* We reverse the ballot. Reversing the ballot and computing
       the margin is equlivalent to marg d c*)

    (* Notion of Unique Winner *)
    Definition unique_winner (marg : cand -> cand -> int) (c : cand) :=
      c_wins marg c = true /\ (forall d, d <> c -> c_wins marg d = false).


    Definition rev_marg (marg : cand -> cand -> int) (c d : cand) :=
      -marg c d. (* We multiply -1 to margin matrix *)

    Lemma marg_rev_marg_opposite :
      forall c d marg, marg c d * rev_marg marg c d <= 0.
    Proof.
      intros c d marg. unfold rev_marg.
      pose proof (marg_neq c d marg).
      rewrite H.
      destruct (marg d c). lia.
      assert (Ht : int.pos p * int.pos p > 0)
        by auto with zarith. lia.

      assert (Ht : int.neg p * int.neg p > 0).
      firstorder. lia.
    Qed.

    Lemma marg_pos_neg :
      forall c d marg, (marg c d > 0 /\ rev_marg marg c d < 0) \/
                  (marg c d = 0 /\ rev_marg marg c d = 0) \/
                  (marg c d < 0 /\ rev_marg marg c d > 0).
    Proof.
      intros c d marg.
      unfold rev_marg.
      lia.
    Qed.

    Lemma marg_and_rev_marg_add_zero :
      forall (c d : cand) (marg : cand -> cand -> int),
        rev_marg marg c d = marg d c.
    Proof.
      intros c d marg. unfold rev_marg.
      rewrite marg_neq. lia.
    Qed.



    Lemma str_min_assoc : forall l marg c d a,
      str marg c (l ++ [a]) d =
      int.min (str marg c l a) (marg a d).
    Proof.
      induction l.
      +  cbn.  auto.
      + intros marg c d a0.  cbn.
        pose proof (IHl marg a d a0).
        rewrite H. lia.
    Qed.


    (* Path from c to d with respect to marg is same as
       path from d to c with respect to rev_marg *)
    Lemma str_and_rev_str : forall l marg c d,
        str marg c l d = str (rev_marg marg) d (rev l) c.
    Proof.
      induction l.
      + intros marg c d.
        unfold rev_marg. cbn; auto.
      + intros marg c d.
        cbn. rewrite str_min_assoc.
        pose proof (IHl marg a d).
        rewrite <- H.
        rewrite marg_and_rev_marg_add_zero.
        lia.
    Qed.



    Lemma path_less :
      forall marg c d k1 k2, k2 >= k1 -> Path marg k2 c d -> Path marg k1 c d.
    Proof.
      intros marg c d k1 k2 Hk Hp.
      induction Hp.
      + constructor. lia.
      + assert (marg c d >= k1) by lia.
        pose (cons marg k1 c d e H0 IHHp).
        auto.
    Qed.

    Lemma path_concat :
      forall marg c d e k1 k2, Path marg k1 c d -> Path marg k2 d e -> Path marg (int.min k1 k2) c e.
    Proof.
      intros marg c d e k1 k2 Hp1 Hp2.
      assert (k1 >= int.min k1 k2 /\ k2 >= int.min k1 k2) by lia.
      destruct H as [H1 H2].
      pose proof (path_less marg c d (int.min k1 k2) k1 H1 Hp1).
      pose proof (path_less marg d e (int.min k1 k2) k2 H2 Hp2).
      clear Hp1; clear Hp2.
      induction H.
      pose proof (cons marg (int.min k1 k2) c d e H H0).
      auto.
      pose proof (IHPath H0).
      pose (cons _ _ _ _ _ H H4). auto.
    Qed.



    Lemma path_with_rev_marg :
      forall k marg c d,
       Path marg k c d <->  Path (rev_marg marg) k d c.
    Proof.
      intros k marg c d.
      split. intro H.
      destruct (path_iterated_marg marg k c d H) as [n Hn].
      destruct (proj1 (iterated_marg_char marg n c d k) Hn) as [l [H1 H2]].
      rewrite  str_and_rev_str in H2.

      assert (length (rev l) <= n)%nat.
      rewrite rev_length. auto.
      pose proof (path_len_iterated_marg (rev_marg marg) n d c k (rev l) H0 H2).
      pose proof (iterated_marg_path (rev_marg marg) n k d c H3). auto.

      intros H.
      destruct (path_iterated_marg (rev_marg marg) k d c H) as [n Hn].
      destruct (proj1 (iterated_marg_char (rev_marg marg) n d c k) Hn) as [l [H1 H2]].
      apply iterated_marg_path with (n := length l).
      apply path_len_iterated_marg with (l := rev l).
      rewrite rev_length. lia.
      rewrite str_and_rev_str.
      rewrite rev_involutive. auto.
    Qed.




    Lemma winner_reversed :
      forall marg c, unique_winner marg c ->
               (exists d, c_wins marg d = false /\ c <> d) ->
               c_wins (rev_marg marg) c = false.
    Proof.
      intros ? ? Hu Hd.
      unfold unique_winner in Hu.
      destruct Hu as [Hu1 Hu2].
      destruct Hd as [d [Hc Hd]].
      rewrite c_wins_false.
      rewrite c_wins_false in Hc.
      rewrite c_wins_true in Hu1.

    Admitted.


    (* Monotonicity *)
    (* we need to prove that margin would remain same in both cases,
       the old ballot and the modified one. *)








  End Propt.





  Section  Count.

    Definition ballot := cand -> nat.

    Inductive State: Type :=
    | partial: (list ballot * list ballot)  -> (cand -> cand -> int) -> State
    | winners: (cand -> bool) -> State.

    Inductive Count (bs : list ballot) : State -> Type :=
    | ax us m : us = bs -> (forall c d, m c d = 0) ->
                Count bs (partial (us, []) m)             (* zero margin      *)
    | cvalid u us m nm inbs : Count bs (partial (u :: us, inbs) m) ->
                              (forall c, (u c > 0)%nat) ->              (* u is valid       *)
                              (forall c d : cand,
                                  ((u c < u d)%nat -> nm c d = m c d + 1) (* c preferred to d *) /\
                                  ((u c = u d)%nat -> nm c d = m c d)     (* c, d rank equal  *) /\
                                  ((u c > u d)%nat -> nm c d = m c d - 1))(* d preferred to c *) ->
                              Count bs (partial (us, inbs) nm)
    | cinvalid u us m inbs : Count bs (partial (u :: us, inbs) m) ->
                             (exists c, (u c = 0)%nat)                 (* u is invalid     *) ->
                             Count bs (partial (us, u :: inbs) m)
    | fin m inbs w (d : (forall c, (wins_type m c) + (loses_type m
                                                            c))):
        Count bs (partial ([], inbs) m)           (* no ballots left  *) ->
        (forall c, w c = true <-> (exists x, d c = inl x)) ->
        (forall c, w c = false <-> (exists x, d c = inr x)) ->
        Count bs (winners w).

    Open Scope nat_scope.

    Definition forall_exists_fin_dec : forall (A : Type) (l : list A) (f : A -> nat),
        {forall x, In x l -> f x > 0} + {exists x, In x l /\ f x = 0} :=
      fun (A : Type) =>
        fix F l f {struct l} :=
        match l with
        | [] => left (fun (x : A) (H : In x []) => match H with end)
        | h :: t =>
          match Nat.eq_dec (f h) 0 with
          | left e =>
            right (ex_intro _  h (conj (in_eq h t) e))
          | right n =>
            match F t f with
            | left Fl =>
              left (fun x H =>
                      match H with
                      | or_introl H1 =>
                        match zerop (f x) with
                        | left e =>
                          False_ind (f x > 0) ((eq_ind h (fun v : A => f v <> 0) n x H1) e)
                        | right r => r
                        end
                      | or_intror H2 => Fl x H2
                      end)
            | right Fr =>
              right
                match Fr with
                | ex_intro _ x (conj Frl Frr) =>
                  ex_intro _ x (conj (in_cons h x t Frl) Frr)
                end
            end
          end
        end.

    Definition ballot_valid_dec : forall b : ballot, {forall c, b c > 0} + {exists c, b c = 0} :=
      fun b => let H := forall_exists_fin_dec cand cand_all in
               match H b with
               | left Lforall => left
                                   (fun c : cand => Lforall c (cand_fin c))
               | right Lexists => right
                                    match Lexists with
                                    | ex_intro _ x (conj _ L) =>
                                      ex_intro (fun c : cand => b c = 0) x L
                                    end
               end.

    Open Scope Z_scope.

    Definition update_marg (p : ballot) (m : cand -> cand -> int) : cand -> cand -> int :=
      fun c d =>  if (Nat.ltb (p c) (p d))%nat
               then (m c d + 1)%int
               else (if (Nat.ltb (p d) (p c))%nat
                     then (m c d -1)%int
                     else m c d).

    Definition listify_v (m : cand -> cand -> int) :=
      map (fun s => (fst s, snd s, m (fst s) (snd s))) (all_pairs cand_all).


    Fixpoint linear_search_v (c d : cand) (m : cand -> cand -> int) l :=
      match l with
      | [] => m c d
      | (c1, c2, k) :: t =>
        match dec_cand c c1, dec_cand d c2 with
        | left _, left _ => k
        | _, _ => linear_search_v c d m t
        end
      end.





    Definition update_marg_listify (p : ballot) (m : cand -> cand -> int) : cand -> cand -> int :=
      let t := update_marg p m in
      let l := listify_v t in
      fun c d => linear_search_v c d t l.

    Theorem equivalent_m_w_v : forall c d m, linear_search_v c d m (listify_v m) = m c d.
    Proof.
      unfold  listify_v.
      intros. induction (all_pairs cand_all); simpl; auto.
      destruct a as (a1, a2). simpl in *.
      destruct (dec_cand c a1).
      destruct (dec_cand d a2). subst. auto.
      auto. auto.
    Qed.

    Corollary equiv_cor : forall p m c d, update_marg p m c d = update_marg_listify p m c d.
    Proof.
      intros p m c d.  unfold update_marg_listify.
      rewrite <- equivalent_m_w_v.
      auto.
    Qed.

    (* correctness of update_marg above *)
    Lemma update_marg_corr: forall m (p : ballot) (c d : cand),
        ((p c < p d)%nat -> update_marg p m c d = m c d + 1) /\
        ((p c = p d)%nat -> update_marg p m c d = m c d) /\
        ((p c > p d)%nat -> update_marg p m c d = m c d - 1).
    Proof.
      intros m p c d.
      split; intros; unfold update_marg.
      destruct (p c <? p d)%nat eqn: H1. lia.
      destruct (p d <? p c)%nat eqn: H2. apply Nat.ltb_lt in H2.
      apply Nat.ltb_ge in H1. lia.
      apply Nat.ltb_ge in H2. apply Nat.ltb_ge in H1. lia.
      split; intros.
      destruct (p c <? p d)%nat eqn: H1.
      apply Nat.ltb_lt in H1. lia.
      apply Nat.ltb_ge in H1. destruct (p d <? p c)%nat eqn: H2. apply Nat.ltb_lt in H2.
      apply Nat.ltb_ge in H1. lia. apply Nat.ltb_ge in H2. lia.
      unfold update_marg.
      destruct (p c <? p d)%nat eqn:H1. apply Nat.ltb_lt in H1. lia.
      apply Nat.ltb_ge in H1. destruct (p d <? p c)%nat eqn: H2.
      apply Nat.ltb_lt in H2. lia. apply Nat.ltb_ge in H2. lia.
    Qed.


     Lemma update_marg_corr_listify: forall m (p : ballot) (c d : cand),
        ((p c < p d)%nat -> update_marg_listify p m c d = m c d + 1) /\
        ((p c = p d)%nat -> update_marg_listify p m c d = m c d) /\
        ((p c > p d)%nat -> update_marg_listify p m c d = m c d - 1).
     Proof.
       intros m p c d. rewrite <- equiv_cor. apply update_marg_corr.
     Qed.


     Definition partial_count_all_counted bs : forall u inbs m,
        Count bs (partial (u, inbs) m) ->  existsT i m, (Count bs (partial ([], i) m)) :=
      fix F u {struct u} :=
        match u with
        | [] =>
          fun inbs m Hc =>
            existT _ inbs (existT _ m Hc)
        | h :: t =>
          fun inbs m Hc =>
            match ballot_valid_dec h with
            | left Hv =>
              let w := update_marg_listify h m in
              F t inbs w (cvalid bs h t m w inbs Hc Hv (update_marg_corr_listify m h))
            | right Hi =>  F t (h :: inbs) m (cinvalid bs h t m inbs Hc Hi)
            end
        end.


    Definition all_ballots_counted (bs : list ballot) :
      existsT i m, Count bs (partial ([], i) m) :=
      partial_count_all_counted bs bs [] (fun _ _ : cand => 0)
                                (ax bs bs (fun _ _ : cand => 0) eq_refl
                                    (fun _ _ : cand => eq_refl)).


     Definition schulze_winners (bs : list ballot) :
      existsT (f : cand -> bool), Count bs (winners f) :=
      let (i, t) := all_ballots_counted bs in
      let (m, p) := t in
      existT  _ (c_wins m) (fin _ _ _ _ (wins_loses_type_dec m) p
                                (c_wins_true_type m) (c_wins_false_type m)).


  End Count.


End Properties.



Section Candidate.

  Inductive cand := A | B | C.
  Definition cand_all := [A; B; C].

  Lemma cand_finite : forall c, In c cand_all.
  Proof.
    unfold cand_all; intro a; repeat induction a || (unfold In; tauto).
  Qed.

  Lemma  cand_eq_dec : forall c d : cand, {c = d} + {c <> d}.
  Proof.
    intros a b;
      repeat induction a;
      repeat (induction b) || (right; discriminate) ||(left; trivial).
  Defined.

  Lemma cand_not_empty : cand_all <> nil.
  Proof. unfold cand_all. intros H. inversion H.
  Qed.

End Candidate.

Definition eschulze_winners_pf :=
  schulze_winners cand cand_all cand_finite cand_eq_dec cand_not_empty.

(*
Definition unicrypt_encryption_library_call :=
  ecount_all_ballot cand (group prime gen publickey). *)

