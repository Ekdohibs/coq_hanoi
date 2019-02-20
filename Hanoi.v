Require Import Psatz.
Require Import List.

Inductive towerid := Zero | One | Two.

Definition otherid (x : towerid) (y : towerid) :=
  match x, y with
  | Zero, Zero => Zero
  | Zero, One => Two
  | Zero, Two => One
  | One, Zero => Two
  | One, One => One
  | One, Two => Zero
  | Two, Zero => One
  | Two, One => Zero
  | Two, Two => Two
  end.


Lemma otherid_diff_1 t1 t2 : t1 <> t2 -> t1 <> otherid t1 t2.
Proof.
  destruct t1; destruct t2; simpl; congruence.
Qed.

Lemma otherid_diff_2 t1 t2 : t1 <> t2 -> otherid t1 t2 <> t2.
Proof.
  destruct t1; destruct t2; simpl; congruence.
Qed.

Lemma otherid_otherid_1 t1 t2 : otherid t1 (otherid t1 t2) = t2.
Proof.
  destruct t1; destruct t2; simpl; auto.
Qed.

Lemma otherid_otherid_2 t1 t2 : otherid (otherid t1 t2) t2 = t1.
Proof.
  destruct t1; destruct t2; simpl; auto.
Qed.


Fixpoint hanoi (n : nat) (from to : towerid) : list (towerid * towerid) :=
  match n with
  | O => nil
  | S n =>
    let int := otherid from to in
    hanoi n from int ++ ((from, to) :: nil) ++ hanoi n int to
  end.

Definition hanoi_config := (list nat * list nat * list nat)%type.

Fixpoint range (n : nat) :=
  match n with
  | O => nil
  | S n1 => range n1 ++ (n1 :: nil)
  end.

Definition hanoi_get_stack (cf : hanoi_config) (x : towerid) :=
  let '(a, b, c) := cf in
  match x with
  | Zero => a
  | One => b
  | Two => c
  end.

Definition hanoi_set_stack (cf : hanoi_config) (x : towerid) (l : list nat) :=
  let '(a, b, c) := cf in
  match x with
  | Zero => (l, b, c)
  | One => (a, l, c)
  | Two => (a, b, l)
  end.

Lemma hanoi_get_stack_eq :
  forall cf, cf = (hanoi_get_stack cf Zero, hanoi_get_stack cf One, hanoi_get_stack cf Two).
Proof.
  intros; destruct cf as [[a b] c]; auto.
Qed.

Inductive hanoi_valid (n : nat) : nat -> hanoi_config -> Prop :=
| HEmpty : hanoi_valid n n (nil, nil, nil)
| HZero : forall k a b c, hanoi_valid n (S k) (a, b, c) -> hanoi_valid n k (k :: a, b, c)
| HOne : forall k a b c, hanoi_valid n (S k) (a, b, c) -> hanoi_valid n k (a, k :: b, c)
| HTwo : forall k a b c, hanoi_valid n (S k) (a, b, c) -> hanoi_valid n k (a, b, k :: c)
.

Lemma hanoi_valid_leq :
  forall n cf k, hanoi_valid n k cf -> k <= n.
Proof.
  intros n cf k H. induction H; lia.
Qed.

Lemma hanoi_valid_values :
  forall n k cf,
    hanoi_valid n k cf ->
    forall x, (In x (fst (fst cf)) \/ In x (snd (fst cf)) \/ In x (snd cf) -> k <= x < n).
Proof.
  intros n k cf H. induction H; intros x Hx; simpl in *.
  - tauto.
  - assert (k < n) by (apply hanoi_valid_leq in H; lia).
    destruct Hx as [[? | ?] | [? | ?]]; try lia; enough (S k <= x < n) by lia; apply IHhanoi_valid; tauto.
  - assert (k < n) by (apply hanoi_valid_leq in H; lia).
    destruct Hx as [? | [[? | ?] | ?]]; try lia; enough (S k <= x < n) by lia; apply IHhanoi_valid; tauto.
  - assert (k < n) by (apply hanoi_valid_leq in H; lia).
    destruct Hx as [? | [? | [? | ?]]]; try lia; enough (S k <= x < n) by lia; apply IHhanoi_valid; tauto.
Qed.

Lemma hanoi_valid_add :
  forall n k cf1 cf2 t1 t2,
    t1 <> t2 ->
    hanoi_get_stack cf1 t1 = k :: hanoi_get_stack cf2 t1 ->
    hanoi_get_stack cf1 t2 = hanoi_get_stack cf2 t2 ->
    hanoi_get_stack cf1 (otherid t1 t2) = hanoi_get_stack cf2 (otherid t1 t2) ->
    hanoi_valid n k cf1 <-> hanoi_valid n (S k) cf2.
Proof.
  intros n k cf1 cf2 t1 t2 Hdiff H1 H2 H3.
  split.
  - intros H. rewrite hanoi_get_stack_eq in H; rewrite hanoi_get_stack_eq.
    inversion H; [destruct t1; congruence| | |];
      destruct t1; destruct t2; simpl in *; try congruence;
        apply hanoi_valid_values with (x := k) in H5; simpl in *; try lia; rewrite ?H1, ?H2, ?H3; simpl; auto.
  - intros H. rewrite hanoi_get_stack_eq.
    destruct t1; destruct t2; simpl in *; try congruence;
      rewrite H1, H2, H3; constructor; rewrite <- hanoi_get_stack_eq; auto.
Qed.

Lemma hanoi_valid_add_range :
  forall n k cf1 cf2 t1 t2,
    t1 <> t2 ->
    hanoi_get_stack cf1 t1 = range k ++ hanoi_get_stack cf2 t1 ->
    hanoi_get_stack cf1 t2 = hanoi_get_stack cf2 t2 ->
    hanoi_get_stack cf1 (otherid t1 t2) = hanoi_get_stack cf2 (otherid t1 t2) ->
    hanoi_valid n O cf1 <-> hanoi_valid n k cf2.
Proof.
  intros n. induction k as [|k].
  - intros cf1 cf2 t1 t2 Hdiff H1 H2 H3; simpl in *.
    replace cf1 with cf2; [reflexivity|].
    rewrite (hanoi_get_stack_eq cf1), (hanoi_get_stack_eq cf2).
    destruct t1; destruct t2; simpl in *; try congruence.
  - intros cf1 cf2 t1 t2 Hdiff H1 H2 H3; simpl in *; rewrite <- app_assoc in *; simpl in *.
    transitivity (hanoi_valid n k (hanoi_set_stack cf2 t1 (k :: hanoi_get_stack cf2 t1))).
    + apply (IHk _ _ _ _ Hdiff);
        destruct t1; destruct t2; destruct cf1 as [[a1 b1] c1]; destruct cf2 as [[a2 b2] c2];
          simpl in *; congruence.
    + apply (hanoi_valid_add _ _ _ _ _ _ Hdiff);
        destruct t1; destruct t2; destruct cf1 as [[a1 b1] c1]; destruct cf2 as [[a2 b2] c2];
          simpl in *; congruence.
Qed.

Inductive make_move : (towerid * towerid) -> hanoi_config -> hanoi_config -> Prop :=
| Move :
    forall t1 t2 k cf1 cf2,
      t1 <> t2 ->
      hanoi_get_stack cf1 t1 = k :: hanoi_get_stack cf2 t1 ->
      hanoi_get_stack cf2 t2 = k :: hanoi_get_stack cf1 t2 ->
      hanoi_get_stack cf1 (otherid t1 t2) = hanoi_get_stack cf2 (otherid t1 t2) ->
      make_move (t1, t2) cf1 cf2.

Lemma make_move_step :
  forall t1 t2 k cf1,
    t1 <> t2 ->
    (exists r, hanoi_get_stack cf1 t1 = k :: r) ->
    exists cf2,
      hanoi_get_stack cf1 t1 = k :: hanoi_get_stack cf2 t1 /\
      hanoi_get_stack cf2 t2 = k :: hanoi_get_stack cf1 t2 /\
      hanoi_get_stack cf1 (otherid t1 t2) = hanoi_get_stack cf2 (otherid t1 t2) /\
      make_move (t1, t2) cf1 cf2.
Proof.
  intros t1 t2 k cf1 Hdiff Hr.
  destruct Hr as [r Hr].
  exists (hanoi_set_stack (hanoi_set_stack cf1 t1 r) t2 (k :: hanoi_get_stack cf1 t2)).
  destruct cf1 as [[a b] c].
  destruct t1; destruct t2; try congruence; simpl in *; repeat (econstructor; simpl in *; auto); auto.
Qed.

Lemma make_move_valid :
  forall n t1 t2 k cf1 cf2,
    hanoi_valid n O cf1 ->
    t1 <> t2 ->
    hanoi_get_stack cf1 t1 = k :: hanoi_get_stack cf2 t1 ->
    hanoi_get_stack cf2 t2 = k :: hanoi_get_stack cf1 t2 ->
    hanoi_get_stack cf1 (otherid t1 t2) = hanoi_get_stack cf2 (otherid t1 t2) ->
    (exists r, hanoi_get_stack cf1 (otherid t1 t2) = range k ++ r) ->
    hanoi_valid n O cf2.
Proof.
  intros n t1 t2 k cf1 cf2 Hvalid Hdiff H1 H2 H3 Hex.
  destruct Hex as [r Hr].
  rewrite (hanoi_valid_add_range _ k _ (hanoi_set_stack cf1 (otherid t1 t2) r) _ _ (otherid_diff_2 _ _ Hdiff)) in Hvalid
    by (destruct t1; destruct t2; destruct cf1 as [[a1 b1] c1]; simpl in *; congruence).
  rewrite (hanoi_valid_add_range _ k _ (hanoi_set_stack cf2 (otherid t1 t2) r) _ _ (otherid_diff_2 _ _ Hdiff))
    by (destruct t1; destruct t2; destruct cf2 as [[a2 b2] c2]; simpl in *; congruence).
  rewrite (hanoi_valid_add _ k _ (hanoi_set_stack (hanoi_set_stack cf1 (otherid t1 t2) r) t1 (hanoi_get_stack cf2 t1)) _ _ Hdiff) in Hvalid
    by (destruct t1; destruct t2; destruct cf1 as [[a1 b1] c1]; simpl in *; congruence).
  assert (Hdiff1 : t2 <> t1) by congruence.
  rewrite (hanoi_valid_add _ k _ (hanoi_set_stack (hanoi_set_stack cf2 (otherid t1 t2) r) t2 (hanoi_get_stack cf1 t2)) _ _ Hdiff1)
    by (destruct t1; destruct t2; destruct cf2 as [[a2 b2] c2]; simpl in *; congruence).
  rewrite hanoi_get_stack_eq; rewrite hanoi_get_stack_eq in Hvalid.
  destruct t1; destruct t2; destruct cf1 as [[a1 b1] c1]; destruct cf2 as [[a2 b2] c2]; simpl in *; congruence.
Qed.

Inductive all_moves_valid (n : nat) : list (towerid * towerid) -> hanoi_config -> hanoi_config -> Prop :=
| AZero : forall cf, hanoi_valid n O cf -> all_moves_valid n nil cf cf
| ACons : forall cf1 cf2 cf3 m r,
    hanoi_valid n O cf1 -> make_move m cf1 cf2 -> all_moves_valid n r cf2 cf3 ->
    all_moves_valid n (m :: r) cf1 cf3.

Lemma all_move_valid_app (n : nat) :
  forall l1 l2 cf1 cf2 cf3,
    all_moves_valid n l1 cf1 cf2 -> all_moves_valid n l2 cf2 cf3 ->
    all_moves_valid n (l1 ++ l2) cf1 cf3.
Proof.
  induction l1 as [|m l1].
  - intros l2 cf1 cf2 cf3 H1 H2; inversion H1; simpl in *. auto.
  - intros l2 cf1 cf2 cf3 H1 H2; inversion H1; simpl in *.
    econstructor; eauto.
Qed.

(*
Inductive is_range (n : nat) : nat -> list nat -> Prop :=
| REmpty : is_range n n nil
| RCons : forall k l, is_range n (S k) l -> is_range n k (k :: l).

Lemma is_range_leq :
  forall n l m, is_range n m l -> m <= n.
Proof.
  intros n. induction l as [|x l].
  - intros m H; inversion H; lia.
  - intros m H; inversion H. specialize (IHl _ H2). lia.
Qed.

Lemma is_range_eq :
  forall n l, is_range n n l -> l = nil.
Proof.
  intros n l H. inversion H; [auto|].
  apply is_range_leq in H0. lia.
Qed.
 *)

Theorem hanoi_solve_valid :
  forall (n : nat) (k : nat) (cf1 : hanoi_config) (t1 t2 : towerid),
    hanoi_valid n O cf1 ->
    t1 <> t2 ->
    (exists r, hanoi_get_stack cf1 t1 = range k ++ r) ->
    exists cf2,
      hanoi_valid n O cf2 /\
      hanoi_get_stack cf1 t1 = range k ++ hanoi_get_stack cf2 t1 /\
      hanoi_get_stack cf2 t2 = range k ++ hanoi_get_stack cf1 t2 /\
      hanoi_get_stack cf1 (otherid t1 t2) = hanoi_get_stack cf2 (otherid t1 t2) /\
      all_moves_valid n (hanoi k t1 t2) cf1 cf2.
Proof.
  intros n. induction k as [|k].
  - intros cf1 t1 t2 Hvalid Hdiff Hr.
    exists cf1; simpl in *.
    repeat (split; auto). constructor; auto.
  - intros cf1 t1 t2 Hvalid Hdiff Hr.
    simpl in *.
    destruct Hr as [r Hr].
    rewrite <- app_assoc in Hr; simpl in Hr.
    destruct (IHk cf1 t1 (otherid t1 t2) Hvalid (otherid_diff_1 _ _ Hdiff) (ex_intro _ _ Hr)) as [cf2 Hcf2].
    destruct Hcf2 as [Hvalid2 [Hstack1 [Hstack3 [Hstack2 Hmoves]]]].
    rewrite otherid_otherid_1 in *.
    assert (Hs2 : hanoi_get_stack cf2 t1 = k :: r) by (rewrite Hr in Hstack1; eapply app_inv_head; eauto).
    destruct (make_move_step _ _ k cf2 Hdiff (ex_intro _ _ Hs2)) as [cf3 Hcf3].
    destruct Hcf3 as [Hst1 [Hst2 [Hst3 Hmove]]].
    assert (Hvalid3 : hanoi_valid n O cf3) by (eapply make_move_valid with (cf1 := cf2); eauto).
    rewrite Hstack3 in Hst3; symmetry in Hst3.
    destruct (IHk cf3 (otherid t1 t2) t2 Hvalid3 (otherid_diff_2 _ _ Hdiff) (ex_intro _ _ Hst3)) as [cf4 Hcf4].
    destruct Hcf4 as [Hvalid4 [Hsta3 [Hsta2 [Hsta1 Hmoves2]]]].
    rewrite otherid_otherid_2 in *.
    exists cf4.
    split; [auto|].
    split; [|split; [|split]].
    + rewrite Hstack1, Hst1, Hsta1, <- app_assoc. auto.
    + rewrite Hsta2, Hst2, Hstack2, <- app_assoc. auto.
    + apply (app_inv_head (range k)). congruence.
    + eapply all_move_valid_app; [exact Hmoves|].
      econstructor; eauto.
Qed.

Lemma range_n_valid :
  forall n, hanoi_valid n O (range n, nil, nil).
Proof.
  intros n. rewrite hanoi_valid_add_range with (cf2 := (nil, nil, nil)) (t1 := Zero) (t2 := One).
  - constructor.
  - congruence.
  - simpl; rewrite app_nil_r; auto.
  - simpl; auto.
  - simpl; auto.
Qed.

Theorem hanoi_solve_complete :
  forall n,
    all_moves_valid n (hanoi n Zero One) (range n, nil, nil) (nil, range n, nil).
Proof.
  intros n.
  destruct (hanoi_solve_valid n n (range n, nil, nil) Zero One (range_n_valid n)) as [final Hfinal].
  - congruence.
  - exists nil. simpl. rewrite app_nil_r; auto.
  - destruct Hfinal as [_ [H1 [H2 [H3 Hvalid]]]]. simpl in *.
    destruct final as [[a b] c]; simpl in *.
    assert (H4 : range n ++ a = range n ++ nil) by (rewrite app_nil_r; auto).
    apply app_inv_head in H4.
    rewrite app_nil_r in H2.
    rewrite H2, <- H3, H4 in Hvalid. auto.
Qed.
