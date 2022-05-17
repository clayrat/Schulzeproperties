From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype ssrint order bigop path.

(*
Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.
*)

Lemma inj_pairl {A B : Type} x : injective [eta (@pair A B)^~ x].
Proof. by apply/(can_inj (g:=fst)). Qed.

Lemma inj_pairr {A B : Type} x : injective [eta (@pair A B) x].
Proof. by apply/(can_inj (g:=snd)). Qed.

Fixpoint all_pairs_row_t {A : Type} (l1 : seq A) (l2 : seq A) : seq (A * A) :=
  if l1 is c :: cs then
    map (fun x => (c, x)) l2 ++ all_pairs_row_t cs l2
  else [::].

Eval compute in all_pairs_row_t [::1;2;3] [::4].

Lemma row_t_correctness {A : eqType} (a1 a2 : A) (l1 l2 : seq A) :
    a1 \in l1 -> a2 \in l2 -> (a1, a2) \in all_pairs_row_t l1 l2.
Proof.
move=>+ H2; elim: l1=>//= c cs IH.
rewrite inE mem_cat; case/orP=>[/eqP ->|/IH ->]; last by rewrite orbT.
by rewrite (mem_map (inj_pairr _)) H2.
Qed.

Definition all_pairs_row {A} (l : seq A) : seq (A * A) :=
  all_pairs_row_t l l.

Lemma all_pairs_row_in {A : eqType} (a1 a2 : A) (l : seq A) :
    a1 \in l -> a2 \in l -> (a1, a2) \in (all_pairs_row l).
Proof. by apply: row_t_correctness. Qed.


Fixpoint all_pairs_col_t {A} (l1 : seq A) (l2 : seq A) : seq (A * A) :=
  if l1 is c :: cs then
    map (fun x => (x, c)) l2 ++ all_pairs_col_t cs l2
  else [::].

Eval compute in all_pairs_col_t [::1;2;3] [::4].


Lemma col_t_correctness {A : eqType} (a1 a2 : A) (l1 l2 : seq A) :
    a1 \in l1 -> a2 \in l2 -> (a2, a1) \in all_pairs_col_t l1 l2.
Proof.
move=>+ H2; elim: l1=>//=c cs IH.
rewrite inE mem_cat; case/orP=>[/eqP ->|/IH ->]; last by rewrite orbT.
by rewrite (mem_map (inj_pairl _)) H2.
Qed.

Definition all_pairs_col {A} (l : seq A) : seq (A * A) :=
  all_pairs_col_t l l.

Lemma all_pairs_col_in {A : eqType} (a1 a2 : A) (l : seq A) :
    a1 \in l -> a2 \in l -> (a2, a1) \in all_pairs_col l.
Proof. by apply: col_t_correctness. Qed.

(* all_pairs computes all the pairs of candidates in l *)
Fixpoint all_pairs {A} (l: seq A): seq (A * A) :=
  if l is c::cs then
    (c, c) :: (all_pairs cs) ++ map (fun x => (c, x)) cs
                             ++ map (fun x => (x, c)) cs
  else [::].

Lemma all_pairsin {A : eqType} (a1 a2 : A) (l : seq A) :
    a1 \in l -> a2 \in l -> (a1, a2) \in all_pairs l.
Proof.
elim: l=>//=c cs IH; rewrite !inE !mem_cat.
case/orP=>[/eqP->|H1]; case/orP=>[/eqP->|H2].
- by rewrite eq_refl.
- by rewrite (mem_map (inj_pairr _)) H2 !orbT.
- by rewrite (mem_map (inj_pairl _)) H1 !orbT.
by rewrite (IH H1 H2) orbT.
Qed.

Theorem length_all_pairs {A} (l : seq A) : size (all_pairs l) = size l * size l.
Proof.
elim: l=>//=x cs IH; rewrite !size_cat !size_map {}IH.
by rewrite mulSnr mulnSr addnA addnS.
Qed.

Theorem length_all_pairs_t_row {A} (l1 l2 : seq A) :
    size (all_pairs_row_t l1 l2) = size l1 * size l2.
Proof.
elim: l1=>//=c cs IH; rewrite size_cat size_map {}IH.
by rewrite mulSn.
Qed.

Theorem length_all_pairs_row {A} (l : seq A) :
    size (all_pairs_row l) = size l * size l.
Proof. by apply: length_all_pairs_t_row. Qed.

Theorem length_all_pairs_t_col {A} (l1 l2 : seq A) :
    size (all_pairs_col_t l1 l2) = size l1 * size l2.
Proof.
elim: l1=>//=c cs IH; rewrite size_cat size_map {}IH.
by rewrite mulSn.
Qed.

Theorem length_all_pairs_col {A} (l : seq A) :
    size (all_pairs_col l) = size l * size l.
Proof. by apply: length_all_pairs_t_col. Qed.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.
Open Scope ring_scope.

(* maxlist return the maximum number in seq l. 0 in case of empty seq *)
Definition maxlist (l : seq int) : int :=
  if l is h::t then
  foldr Order.max h t   (*\big[Order.max/h]_(i <- t) i*)
  else 0%:Z.

(* give two numbers m and n with proof that m < n then it return the
   proof that maximum of m and n is n *)
Lemma max_two_integer (m n : int) : m < n -> Order.max m n = n.
Proof. by move=>H; apply/eqP; rewrite eq_maxr; apply: ltW. Qed.

(* Shows the prop level existence of element x in seq l >= s if maximum element of
   seq l >= s  *)
Lemma max_of_nonempty_list (l : seq int) (s : int) :
    ~~ nilp l ->
    reflect (exists2 x, x \in l & s <= x) (s <= maxlist l).
Proof.
case: l=>//=h t _; rewrite foldrE.
suff: (s <= \big[Order.max/h]_(j <- t) j = has (>= s) (h :: t)).
- by move=>->; apply: hasP.
rewrite /= -big_has; case H: (s <= h)=>/=; last first.
- rewrite (@big_morph _ _ (>= s) false orb) //.
  by move=>x y; rewrite le_maxr.
elim: t=>/=; first by rewrite big_nil.
by move=>t ts IH; rewrite big_cons le_maxr IH orbT.
Qed.

(*
Lemma max_of_nonempty_list {A : eqType} (l : seq A) (s : int) (f : A -> int) :
    ~~ nilp l ->
    reflect (exists2 x, x \in l & s <= f x) (s <= maxlist (map f l)).
Proof.
move=>H; have Hm: ~~ nilp (map f l) by rewrite /nilp size_map.
apply: equivP; first by apply: max_of_nonempty_list'.
split; case=>x.
- by case/mapP=>y Hy -> Hs; exists y.
by move=>Hx Hs; exists (f x)=>//; apply/map_f.
Qed.
*)

Lemma max_of_nonempty_list_eq (l : seq int) (s : int) :
    ~~ nilp l ->
    s == maxlist l -> exists2 x, x \in l & s = x.
Proof.
case: l=>//=h t _; rewrite foldrE big_seq_cond.
elim/big_ind: _.
- by move/eqP=>->; exists h=>//=; rewrite inE eq_refl.
- by move=>x y Hx Hy; rewrite maxElt; case: ifP.
by move=>i; rewrite andbT=>Hi /eqP ->; exists i=>//; rewrite inE Hi orbT.
Qed.

(*
Lemma max_of_nonempty_list_equal :
  forall (A : Type) (l : seq A) (H : l <> nil) (H1 : forall x y : A, {x = y} + {x <> y}) (s : Z) (f : A -> Z),
    maxlist (map f l) = s -> exists (x:A), \in x l /\ f x = s.
*)

(* minimum of two integers m and n is >= s then both numbers are
   >= s *)
   (*
Lemma z_min_lb (m n s : int) : Order.min m n >= s <-> (m >= s) && (n >= s).
Proof. by rewrite le_minr. Qed.
*)
(* if size of seq l >= 1 then  l is nonempty *)
(*
Lemma exists_list {A} (l : seq A) (n : nat) : (0 < size l)%nat -> exists a ls, l = a :: ls.
Proof. by case: l=>//= a ls _; exists a, ls. Qed.
*)
(* If a in seq l and x in not in seq l then x <> a *)
(*
Lemma not_equal_elem {A : eqType} (a x : A) (l : seq A) :
    a \in l -> x \notin l -> x != a.
Proof. by move=>Ha; apply: contra=>/eqP->. Qed.
*)
(* all the elements appearing in l also appears in seq c *)
Definition covers {A : eqType} (c l : seq A) := {subset l <= c}.

(*
Lemma size_ind {T} P :
  (forall xs, size xs = 0 -> P xs) ->
  (forall n, (forall xs, size xs <= n -> P xs)%N -> forall xs, size xs <= n.+1 -> P xs)%N ->
  forall (xs : seq T), P xs.
Proof.
(* from https://stackoverflow.com/a/45883068/919707 *)
move=>H0 Hn xs; move: {2}(size _) (leqnn (size xs)) =>n; elim: n xs=>[|n IH] xs.
- by rewrite leqn0=>/eqP; apply: H0.
by apply/Hn/IH.
Qed.
*)

(* split the seq l at duplicate elements given the condition that c covers l *)
Lemma list_split_dup_elem {A : eqType} (c l : seq A) (x0 : A) :
    (size l > size c)%N ->
    covers c l -> exists (a : A) l1 l2 l3, l = l1 ++ (a :: l2) ++ (a :: l3).
Proof.
move=>Hs Hc; suff: ~~ uniq l; last first.
- rewrite -ltn_size_undup; apply/leq_ltn_trans/Hs.
  apply: uniq_leq_size; first by exact: undup_uniq.
  by move=>z Hz; apply: Hc; apply/mem_subseq/Hz; exact: undup_subseq.
case/(uniqPn x0)=>i[j][Hij Hj E].
move: (ltn_trans Hij Hj)=>/[dup] Hi /(mem_nth x0); rewrite -has_pred1=>H1.
rewrite -(cat_take_drop i l) (drop_nth x0 Hi).
rewrite -(cat_take_drop (j-i.+1) (drop i.+1 l)) drop_drop subnK // (drop_nth x0 Hj).
exists (nth x0 l j), (take i l), (take (j - i.+1) (drop i.+1 l)), (drop j.+1 l).
by rewrite E.
Qed.

(* if maximum of two numbers m, n >= s then either m >= s or
   n >= s *)
Lemma z_max_lb (m n s : int) : Order.max m n >= s <-> (m >= s) || (n >= s).
Proof. by rewrite le_maxr. Qed.

(* if size of seq l is > n then there is a natural number
   p such that p + n = size of seq l *)
Lemma list_and_num {A} (n : nat) (l : seq A) :
    (size l > n)%N -> exists p, (size l = p + n)%N.
Proof. by move=>H; exists (size l - n); rewrite subnK //; apply: ltnW. Qed.

(* if forallb f l returns false then existance of element x in seq l
   such that f x = false, and if x is in seq l and f x = false then
   forallb f l will evaluate to false *)
(*
Lemma forallb_false {A : eqType} (f : pred A) (l : seq A) :
    reflect (exists2 x, x \in l & ~~ f x) (~~ all f l).
Proof. by exact: allPn. Qed.
*)

Lemma upperbound_of_nonempty_list (l : seq int) (s : int) :
    ~~ nilp l ->
    reflect (forall x, x \in l -> x <= s) (maxlist l <= s).
Proof.
case: l=>//=h t _; rewrite foldrE.
suff: (\big[Order.max/h]_(x <- t) x <= s = all (<= s) (h :: t)).
- by move=>->; apply: allP.
rewrite /= -big_all; case H: (h <= s)=>/=.
- rewrite (@big_morph _ _ (fun z => z <= s) true andb) //.
  by move=>x y; rewrite le_maxl.
elim: t=>/=; first by rewrite big_nil.
by move=>t ts IH; rewrite big_cons le_maxl IH andbF.
Qed.

(*
Lemma upperbound_of_nonempty_list' {A : eqType} (l : seq A) (s : int) (f : A -> int) :
    ~~ nilp l ->
    reflect (forall x, x \in l -> f x <= s) (maxlist (map f l) <= s).
Proof.
move=>H; have Hm: ~~ nilp (map f l) by rewrite /nilp size_map.
apply: equivP; first by apply: upperbound_of_nonempty_list.
split=>H0 x.
- by move=>Hx; apply: H0; apply/map_f.
by case/mapP=>z Hz ->; apply: H0.
Qed.
*)

(*
(*  Shows the type level existence of element x in seq l >=  s if maximum element of
   seq l >= s *)
Lemma max_of_nonempty_list_type {A : eqType} (l : seq A) :
  ~~ nilp l ->
    (s : Z) (f : A -> Z), maxlist (map f l) >= s -> existsT (x:A), \in x l /\ f x >= s.
Proof.
  intros A.
  assert (Hm : forall (a b : A) (l : seq A) (f : A -> Z),
             maxlist (f a :: map f (b :: l)) = Z.max (f a) (maxlist (map f (b :: l)))) by auto.
  refine (fix F l {struct l} :=
            fun H H1 s f =>
              match l as l0 return (l = l0 -> l0 <> [] ->
                                    maxlist (map f l0) >= s ->
                                    existsT (x : A), \in x l0 /\ f x >= s) with
              | [] => fun _ H =>  match H eq_refl with end
              | h :: t =>
                fun Heq Hn =>
                  match t as t0 return (t = t0 -> (h :: t0) <> [] ->
                                        maxlist (map f (h :: t0)) >= s ->
                                        existsT (x : A), \in x (h :: t0) /\ f x >= s) with
                  | [] => fun _ H1 H2 => existT _ h (conj (in_eq h []) H2)
                  | h1 :: t1 =>
                    let Hmax := (Z_ge_lt_dec (f h) (maxlist (map f (h1 :: t1)))) in
                    match Hmax with
                    | left e => fun H1 H2 H3 => _
                    | right r => fun H1 H2 H3 => _
                    end
                  end eq_refl Hn
            end eq_refl H).

  rewrite map_cons in H3. rewrite Hm in H3.
  apply Z.ge_le in e. pose proof (Z.max_l _ _ e) as Hmx.
  rewrite Hmx in H3.
  exists h. intuition.


  rewrite map_cons in H3. rewrite Hm in H3.
  pose proof (max_two_integer _ _ r) as Hmx.
  rewrite Hmx in H3.
  assert (Ht : [] <> h1 :: t1) by apply nil_cons.
  apply not_eq_sym in Ht.
  rewrite <- H1 in H2, H3, Hmx, Ht.
  specialize (F _ Ht H4 s f H3).
  destruct F as [x [Fin Fx]]. rewrite <- H1.
  exists x. intuition.
Defined.
*)

(*
(* if forallb f l returns false then type level existance of element x in seq l
   such that f x = false *)
Lemma forallb_false_type {A} (f : pred A) (l : seq A) :
    ~~ all f l -> existsT x, \in x l /\ f x = false.
Proof.
  refine (fun A f =>
            fix F l :=
            match l as l0 return (forallb f l0 = false ->
                                  existsT x, \in x l0 /\ f x = false) with
            | [] => fun H => match (diff_true_false H) with end
            | h :: t =>
              fun H => match f h as v return (f h = v -> existsT x, \in x (h :: t) /\ f x = false) with
                    | false => fun H1 => existT _ h (conj (in_eq h t) H1)
                    | true => fun H1 => _
                    end eq_refl
            end).

  simpl in H. rewrite H1 in H. simpl in H. pose proof (F t H) as Ft.
  destruct Ft as [x [Fin Fx]]. exists x. intuition.
Defined.
*)
Lemma filter_empty {A : eqType} (l : seq A) (f : pred A) :
    reflect (forall x, x \in l -> ~~ f x) (nilp (filter f l)).
Proof.
suff: (nilp [seq x <- l | f x] = all (negb \o f) l).
- by move=>->; apply: allP.
rewrite /nilp -all_pred0 all_filter; apply: eq_in_all.
by move=>z Hz /=; case: (f z).
Qed.

Lemma complementary_filter_perm {A : eqType} (p: pred A) (l: seq A):
  perm_eq l (filter p l ++ filter (predC p) l).
Proof. by rewrite perm_sym perm_filterC. Qed.

Lemma complementary_filter_In {A : eqType} (l : seq A) (f : pred A) (g : pred A) :
    (forall x, x \in l -> f x = ~~ g x) ->
    perm_eq l (filter f l ++ filter g l).
Proof.
move=>H; rewrite -(perm_filterC f) perm_cat2l.
rewrite (eq_in_filter (a2:=g)) // => z Hz /=.
by rewrite H // negbK.
Qed.

(*
Lemma not_equal_elem : forall (A : Type) (a x : A) (l : seq A),
    \in a l -> ~ \in x l -> x <> a.
Proof.
  intros A a x l H1 H2.
  induction l. inversion H1.
  specialize (proj1 (not_in_cons x a0 l) H2); intros.
  simpl in H1. destruct H as [H3 H4]. destruct H1.
  subst. assumption. apply IHl. assumption. assumption.
Qed. *)

Theorem transitive_dec_first {A} (P : A -> A -> Prop) :
   (forall c d, decidable (P c d)) ->
   forall (x y z : A), decidable (P x y -> P y z -> P x z).
Proof.
move=>H x y z.
apply/decP/implyPP; first by apply/sumboolP/H.
by apply: implyPP; apply/sumboolP/H.
Qed.

Theorem transitive_dec_second {A : eqType} (P : A -> A -> Prop) (l : seq A):
   (forall c d, decidable (P c d)) ->
   forall (x y : A), decidable (forall z, z \in l -> P x y -> P y z -> P x z).
Proof.
move=>H x y; elim: l=>[|h t]; first by left.
case: (transitive_dec_first _ H x y h)=>H1; last first.
- move=>_; right; move: H1; apply: contra_not; apply.
  by rewrite inE eq_refl.
case=>IH.
- left=>z; rewrite inE; case/orP; last by apply: IH.
  by move/eqP=>->.
right; move: IH; apply: contra_not=>+ z Hz; apply.
by rewrite inE Hz orbT.
Qed.

Theorem transitive_dec_third {A : eqType} (P : A -> A -> Prop) (l1 l2 : seq A):
    (forall c d, decidable (P c d)) ->
    forall (x : A), decidable (forall y z, y \in l1 -> z \in l2 -> P x y -> P y z -> P x z).
Proof.
move=>H x; elim: l1=>[|h t]; first by left.
case: (transitive_dec_second _ l2 H x h)=>H1; last first.
- move=>_; right; move: H1; apply: contra_not=>+ z; apply.
  by rewrite inE eq_refl.
case=>IH.
- left=>y z; rewrite inE; case/orP; last by apply: IH.
  by move/eqP=>->; apply: H1.
right; move: IH; apply: contra_not=>+ y z Hy; apply.
by rewrite inE Hy orbT.
Qed.

Theorem transitive_dec_fourth {A : eqType} (P : A -> A -> Prop) (l1 l2 l3 : seq A):
    (forall c d, decidable (P c d)) ->
    decidable (forall x y z, x \in l1 -> y \in l2 -> z \in l3 -> P x y -> P y z -> P x z).
Proof.
move=>H; elim: l1=>[|h t]; first by left.
case: (transitive_dec_third _ l2 l3 H h)=>H1; last first.
- move=>_; right; move: H1; apply: contra_not=>+ y z; apply.
  by rewrite inE eq_refl.
case=>IH.
- left=>x y z; rewrite inE; case/orP; last by apply: IH.
  by move/eqP=>->; apply: H1.
right; move: IH; apply: contra_not=>+ x y z Hx; apply.
by rewrite inE Hx orbT.
Qed.

Theorem transitive_dec {A : eqType} (P : A -> A -> Prop) (l : seq A):
    (forall c d, decidable (P c d)) ->
    decidable (forall x y z, x \in l -> y \in l -> z \in l -> P x y -> P y z -> P x z).
Proof. by move=>H; apply: transitive_dec_fourth. Qed.

(* End of List Lemma file *)
