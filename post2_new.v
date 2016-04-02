Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import vecs_new.
Require Import andnot_new.
Require Import classical_new.
Require Import post_new.

Lemma index_dec : forall (n : nat)(i j : fin n), i=j\/i<>j.
Proof.
  intros.
  induction n.
  destruct i.
  destruct i,j.
  destruct u,u0.
  left; reflexivity.
  right; discriminate.
  right; discriminate.
  destruct (IHn f f0).
  left; rewrite H; reflexivity.
  right; intro.
  apply H.
  injection H0.
  tauto.
Qed.

Lemma fp_dec : forall (n : nat)(f : conn n), decidable0 (f_preserving f).
Proof.
  intros.
  destruct (bool_destr (f (f_vec n))).
  left; exact H.
  right; intro.
  rewrite H0 in H.
  discriminate.
Qed.

Lemma tp_dec : forall (n : nat)(f : conn n), decidable0 (t_preserving f).
Proof.
  intros.
  destruct (bool_destr (f (t_vec n))).
  right; intro.
  rewrite H0 in H.
  discriminate.
  left; exact H.
Qed.

Lemma mon_dec : forall (n : nat)(f : conn n), decidable0 (monotone f).
Proof.
  intros.
  unfold monotone.
  assert (decidable0 (exists x y, ~ (vec_le n x y -> bool_le (f x) (f y)))).
  apply vec_bool_ExEM.
  intro x.
  apply vec_bool_ExEM.
  apply dec_neg.
  intro y.
  apply impl_dec0.
  apply le_dec.
  apply bool_le_dec.
  destruct H.
  right.
  intro.
  destruct H as [v [w Hvw]].
  apply Hvw.
  apply H0.
  left.
  intros.
  destruct (bool_le_dec (f x) (f y)).
  exact H1.
  elim H.
  exists x,y.
  intro.
  apply H1.
  apply H2.
  exact H0.
Qed.

Lemma sd_dec : forall (n : nat)(f : conn n), decidable0 (self_dual f).
Proof.
  intros.
  unfold self_dual.
  assert (decidable0 (exists x, f x <> (dual f) x)).
  apply vec_bool_ExEM.
  intro v.
  destruct (f v); destruct (dual f v).
  right; intro; elim H; reflexivity.
  left; discriminate.
  left; discriminate.
  right; intro; elim H; reflexivity.
  destruct H.
  right.
  intro.
  destruct H as [v Hv].
  apply Hv.
  apply H0.
  left.
  intro v.
  destruct (bool_dec (f v) (dual f v)).
  exact e.
  elim H.
  exists v; exact n0.
Qed.

Lemma counting_dec : forall (n : nat)(f : conn n), decidable0 (counting f).
Proof.
  intros.
  assert (decidable0 (exists i, ~ (is_dummy f i \/ is_counted f i))).
  apply finExEM.
  apply dec_neg.
  apply or_dec1.
  intro i; apply dummy_dec.
  intro i; apply count_dec.
  destruct H.
  right.
  intro.
  destruct H as [i Hi].
  apply Hi.
  apply H0.
  left.
  intro i.
  destruct (dummy_dec f i).
  left; exact H0.
  destruct (count_dec f i).
  right; exact H1.
  elim H.
  exists i.
  intro.
  destruct H2; contradiction.
Qed.

Definition upward_closed(X : forall n:nat, conn n -> Prop) :=
  forall (n : nat)(f : conn n), Definable X f -> X n f.

(*False/Truth-preserving functions are closed under composition*)
Lemma bp_comp(n k : nat)(gs : vec (conn k) n)(b : bool) : (forall i : fin n,
     item_at (conn k) n i gs (const_vec k b) = b)
  -> vec_ap bool n gs (const_vec k b) = const_vec n b.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  destruct gs.
  assert (item_at (conn k) 1 (inl tt) (c,tt) (const_vec k b) = b).
  simpl.
  apply (H (inl tt)).
  simpl in H0.
  simpl.
  rewrite H0.
  rewrite IHn.
  reflexivity.
  intro i.
  apply (H (inr i)).
Qed. 

(*only fp functions can be defined from a set of fp connectives*)
Lemma fp_upward_closed : upward_closed f_preserving.
Proof.
  unfold upward_closed.
  intros.
  unfold f_preserving.
  induction H.
  apply H.
  auto.
  unfold proj, f_vec.
  rewrite const_vec_constant.
  reflexivity.
  unfold comp, f_vec.
  rewrite bp_comp.
  exact IHDefinable.
  exact H1.
  rewrite <- H0.
  exact IHDefinable.
Qed.

Lemma tp_upward_closed : upward_closed t_preserving.
Proof.
  unfold upward_closed.
  intros.
  unfold t_preserving.
  induction H.
  apply H.
  auto.
  unfold proj, t_vec.
  rewrite const_vec_constant.
  reflexivity.
  unfold comp, t_vec.
  rewrite bp_comp.
  exact IHDefinable.
  exact H1.
  rewrite <- H0.
  exact IHDefinable.
Qed.

(*composition preserves monotonicity*)
Lemma comp_less(n k : nat)(gs : vec (conn k) n)(v w : vec bool k) :
  (forall i : fin n, monotone (item_at (conn k) n i gs)) ->
  vec_le k v w -> vec_le n (vec_ap bool n gs v) (vec_ap bool n gs w).
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  destruct gs as [g gs].
  simpl.
  split.
  pose (Gmon := H (inl tt)).
  simpl in Gmon.
  apply Gmon.
  exact H0.
  apply IHn.
  intro i.
  exact (H (inr i)).
Qed.

(*only monotone functions can be defined from a set of tp connectives*)
Lemma mon_upward_closed : upward_closed monotone.
Proof.
  unfold upward_closed.
  intros.
  induction H.
  exact H.
  intros v w.
  intro.
  destruct v,w.
  destruct (const 0 x tt); reflexivity.
  intros v w.
  intro.
  apply vec_le_correct.
  exact H.
  intros v w.
  intro.
  unfold comp.
  apply IHDefinable.
  apply comp_less.
  exact H1.
  exact H2.
  intros v w.
  rewrite <- H0.
  rewrite <- H0.
  apply IHDefinable.
Qed.

Lemma vec_ap_negated(n k : nat)(gs : vec (conn k) n)(v : vec bool k) :
  (forall i : fin n, self_dual (item_at (conn k) n i gs)) ->
  vec_ap bool n gs (negated k v) = negated n (vec_ap bool n gs v).
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  destruct gs as [g gs].
  simpl.
  rewrite IHn.
  pose (Gsd := H (inl tt)).
  simpl in Gsd.
  rewrite Gsd.
  unfold dual.
  rewrite negated_invol.
  reflexivity.
  intro i.
  exact (H (inr i)).
Qed.

(*only self-dual functions can be defined from a set of tp connectives*)
Lemma sd_upward_closed : upward_closed self_dual.
Proof.
  unfold upward_closed.
  intros.
  induction H.
  exact H.
  intro v.
  absurd (const 1 x [true] = dual (const 1 x) [true]).
  unfold const, dual.
  intro.
  apply (no_fixpoint_negb x).
  symmetry; exact H0.
  apply IHDefinable.
  intro v.
  unfold proj, dual.
  rewrite negated_correct.
  rewrite negb_involutive.
  reflexivity.
  unfold self_dual, comp.
  intro v; unfold dual.
  rewrite vec_ap_negated.
  rewrite IHDefinable.
  unfold dual.
  reflexivity.
  exact H1.
  intro v.
  rewrite <- H0.
  unfold dual.
  rewrite <- H0.
  apply IHDefinable.
Qed.


(*the index being projected to is a counted variable*)
Lemma eq_count : forall (n : nat)(i : fin n), is_counted (proj n i) i.
Proof.
  intros.
  intro v.
  unfold proj.
  rewrite neg_at_correct.
  rewrite negb_involutive.
  reflexivity.
Qed.

(*negating an index does not change the other indices*)
Lemma neq_neg : forall (n : nat)(i j : fin n)(v : vec bool n), i <> j -> 
  item_at bool n i v = item_at bool n i (neg_at n v j).
Proof.
  intros.
  induction n.
  destruct i.
  destruct i,j,v.
  destruct u,u0.
  elim H; reflexivity.
  destruct u; simpl.
  reflexivity.
  destruct u.
  simpl.
  reflexivity.
  simpl.
  rewrite (IHn f f0).
  reflexivity.
  intro.
  apply H.
  rewrite H0; reflexivity.
Qed. 

(*indices other than the projected index are dummies*)
Lemma neq_dummy : forall (n : nat)(i j : fin n), i<>j -> is_dummy (proj n i) j.
Proof.
  intros.
  intro v.
  unfold proj.
  exact (neq_neg n v H).
Qed.

Fixpoint dotprod(n : nat) : vec bool n -> vec bool n -> bool :=
  match n as n return vec bool n -> vec bool n -> bool with
  |0     => fun v w => false
  |(S m) => fun v w => xorb (andb (vhead v) (vhead w)) (dotprod m (vtail v) (vtail w))
  end.

Lemma dotprod_lemma_f : forall (n : nat)(v w : vec bool n)(i : fin n),
  item_at bool n i v = false -> dotprod n v (neg_at n w i) = dotprod n v w.
Proof.
  intros.
  induction n.
  destruct i.
  destruct v,w.
  destruct i.
  destruct u.
  simpl in H.
  rewrite H.
  simpl; reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  exact H.
Qed.

Lemma dotprod_lemma_t : forall (n : nat)(v w : vec bool n)(i : fin n),
  item_at bool n i v = true -> dotprod n v (neg_at n w i) = negb (dotprod n v w).
Proof.
  intros.
  induction n.
  destruct i.
  destruct v,w.
  destruct i.
  destruct u.
  simpl in H.
  rewrite H.
  simpl.
  rewrite negb_xorb_l.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite negb_xorb_r.
  reflexivity.
  exact H.
Qed.

Definition affine(n : nat)(v : vec bool n)(b : bool)(x : vec bool n) : bool :=
  xorb (dotprod n v x) b.

Lemma affine_are_counting : forall (n : nat)(v : vec bool n)(b : bool),
  counting (affine n v b).
Proof.
  unfold affine.
  intros.
  intro i.
  destruct (bool_destr (item_at bool n i v)).
  left.
  intro w.
  rewrite (dotprod_lemma_f n v w i H).
  reflexivity.
  right.
  intro w.
  rewrite (dotprod_lemma_t n v w i H).
  rewrite negb_xorb_l.
  rewrite negb_involutive.
  reflexivity.
Qed.

Lemma affine_ext_counting : forall (n : nat)(f : conn n),
  (exists (v : vec bool n)(b : bool), f [=] (affine n v b)) -> counting f.
Proof.
  intros.
  destruct H as [v [b Hf]].
  intro i.
  destruct (affine_are_counting n v b i).
  left.
  intro w.
  rewrite Hf.
  rewrite Hf.
  apply H.
  right.
  intro w.
  rewrite Hf.
  rewrite Hf.
  apply H.
Qed.

Definition bool_rep(n : nat)(f : conn n) : vec bool n :=
  to_vec n (fun i => xorb (f (f_vec n)) (f (neg_at n (f_vec n) i))).

Lemma bool_rep_correct_dummy(n : nat)(f : conn n)(i : fin n) : is_dummy f i ->
  item_at bool n i (bool_rep f) = false.
Proof.
  intro.
  unfold bool_rep.
  rewrite to_vec_correct.
  rewrite H.
  apply xorb_nilpotent.
Qed.

Lemma bool_rep_correct_count(n : nat)(f : conn n)(i : fin n) : is_counted f i ->
  item_at bool n i (bool_rep f) = true.
Proof.
  intro.
  unfold bool_rep.
  rewrite to_vec_correct.
  rewrite H.
  rewrite <- negb_xorb_l.
  rewrite xorb_nilpotent.
  reflexivity.
Qed.

Lemma counting_lemma : forall (n : nat)(f : conn n), counting f -> 
  forall v, dotprod n (bool_rep f) v = xorb (f (f_vec n)) (f v).
Proof.
  intros.
  induction n.
  unfold f_vec; simpl.
  destruct v.
  symmetry; apply xorb_nilpotent.
  simpl.
  assert (to_vec n (fun j => 
    xorb (f (f_vec (S n))) (f (false, neg_at n (const_vec n false) j))) = bool_rep (fun v => f (false, v))).
  unfold bool_rep.
  apply vec_ext.
  intro i.
  rewrite to_vec_correct.
  rewrite to_vec_correct.
  simpl; reflexivity.
  rewrite H0. 
  rewrite IHn.
  destruct (H (inl tt)).
  assert (f (f_vec (S n)) = f (true , const_vec n false)).
  apply H1.
  assert (f (false , vtail v) = f v).
  destruct v.
  destruct b.
  apply H1.
  reflexivity.
  rewrite H2, H3.
  rewrite xorb_nilpotent.
  simpl.
  rewrite <- H2.
  unfold f_vec; simpl.
  destruct (xorb (f (false , const_vec n false))); reflexivity.
  assert (f (f_vec (S n)) = negb (f (true , const_vec n false))).
  apply H1.
  rewrite H2.
  rewrite <- negb_xorb_l.
  rewrite xorb_nilpotent.
  rewrite <- H2.
  simpl.
  destruct v.
  simpl.
  destruct b.
  assert (f (false, v) = negb (f (true, v))).
  apply H1.
  rewrite H3.
  rewrite negb_xorb_r.
  rewrite negb_involutive.
  reflexivity.
  rewrite xorb_false_l.
  reflexivity.
  intro j.
  destruct (H (inr j)).
  left.
  intro w.
  apply H1.
  right.
  intro w.
  apply H1.
Qed.

Lemma counting_are_affine : forall (n : nat)(f : conn n), counting f -> 
  sigT (fun (p : (vec bool n) * bool) => f [=] affine n (fst p) (snd p)).
Proof.
  intros.
  exists ( (bool_rep f) , (f (f_vec n)) ).
  intro w.
  unfold affine.
  apply xorb_move_l_r_2.
  symmetry.
  rewrite xorb_comm.
  apply counting_lemma.
  exact H.
Qed.

Fixpoint vec_add(n : nat) : vec bool n -> vec bool n -> vec bool n :=
  match n with
  |0     => fun v w => (tt : vec bool 0)
  |(S m) => fun v w => ( xorb (vhead v) (vhead w) , vec_add m (vtail v) (vtail w) )
  end.

Lemma vec_add_correct : forall (n : nat)(v w : vec bool n)(i : fin n),
  item_at bool n i (vec_add n v w) = xorb (item_at bool n i v) (item_at bool n i w).
Proof.
  intros.
  induction n.
  destruct i.
  destruct v,w.
  destruct i.
  destruct u; simpl.
  reflexivity.
  simpl.
  apply IHn.
Qed.

Lemma dotprod_l_dist : forall (n : nat)(v w x : vec bool n),
  dotprod n v (vec_add n w x) = xorb (dotprod n v w) (dotprod n v x).
Proof.
  intros.
  induction n.
  simpl; reflexivity.
  destruct v,w,x.
  simpl.
  rewrite IHn.
  destruct b,b0,b1,(dotprod n v v1),(dotprod n v v0); reflexivity.
Qed.

Lemma dotprod_r_dist : forall (n : nat)(v w x : vec bool n),
  dotprod n (vec_add n v w) x = xorb (dotprod n v x) (dotprod n w x).
Proof.
  intros.
  induction n.
  simpl; reflexivity.
  destruct v,w,x.
  simpl.
  rewrite IHn.
  destruct b,b0,b1,(dotprod n v v1),(dotprod n v0 v1); reflexivity.
Qed.

Definition matrix(m n : nat) : Set := vec (vec bool n) m.

Fixpoint appl(m n : nat) : matrix m n -> vec bool n -> vec bool m :=
  match m as m return matrix m n -> vec bool n -> vec bool m with
  |0     => fun M v => (tt : vec bool 0)
  |(S k) => fun M v => ( dotprod n (vhead M) v , appl k n (vtail M) v )
  end.

Lemma appl_correct : forall (m n : nat)(M : matrix m n)(v : vec bool n)(i : fin m),
  item_at bool m i (appl m n M v) = dotprod n (item_at _ m i M) v.
Proof.
  intros.
  induction m.
  destruct i.
  destruct M.
  destruct i.
  destruct u; simpl.
  reflexivity.
  simpl.
  apply IHm.
Qed.

Fixpoint l_cat(m n : nat) : vec bool m -> matrix m n -> matrix m (S n) :=
  match m as m return vec bool m -> matrix m n -> matrix m (S n) with
  |0     => fun v M => (tt : vec (vec bool (S n)) 0)
  |(S k) => fun v M => ( (vhead v , vhead M) , (l_cat k n (vtail v) (vtail M)) )
  end.

Lemma l_cat_app_f(m n : nat) : forall (c : vec bool m)(N : matrix m n)(v : vec bool n),
  appl m (S n) (l_cat m n c N) (false , v) = (appl m n N v).
Proof.
  intros.
  induction m.
  simpl; reflexivity.
  simpl.
  rewrite andb_false_r.
  rewrite xorb_false_l.
  rewrite IHm.
  reflexivity.
Qed.

Lemma l_cat_app_t(m n : nat) : forall (c : vec bool m)(N : matrix m n)(v : vec bool n),
  appl m (S n) (l_cat m n c N) (true , v) = vec_add m c (appl m n N v).
Proof.
  intros.
  induction m.
  simpl; reflexivity.
  simpl.
  rewrite andb_true_r.
  rewrite IHm.
  reflexivity.
Qed. 

Fixpoint transpose(m n : nat) : matrix m n -> matrix n m :=
  match m as m return matrix m n -> matrix n m with
  |0     => fun M => const_vec n (tt : vec bool 0)
  |(S k) => fun M => l_cat n k (vhead M) (transpose k n (vtail M))
  end.

Lemma assoc_lemma : forall (m n : nat)(M : matrix m n)(v : vec bool m)(w : vec bool n),
  dotprod m v (appl m n M w) = dotprod n (appl n m (transpose m n M) v) w.
Proof.
  intros.
  induction m.
  induction n.
  simpl; reflexivity.
  destruct v,w.
  simpl.
  assert ((const_vec n tt) = transpose 0 n M).
  reflexivity.
  rewrite H.
  rewrite <- IHn.
  simpl.
  reflexivity.
  destruct M as [r N].
  destruct v as [v0 v'].
  simpl.
  rewrite IHm.
  destruct v0.
  simpl.
  rewrite l_cat_app_t.
  rewrite dotprod_r_dist.
  reflexivity.
  rewrite xorb_false_l.
  rewrite l_cat_app_f.
  reflexivity.
Qed.

(*counting functions are closed under composition*)
Lemma counting_compose(n k: nat)(f : conn n)(gs : vec (conn k) n) :
  counting f -> (forall i : fin n, counting (item_at (conn k) n i gs))
  -> counting (comp k f gs).
Proof.
  intros.
  apply affine_ext_counting.
  destruct (counting_are_affine H) as [[v b] Hf].
  pose (g := fun i => item_at (conn k) n i gs).
  assert (forall i, sigT (fun (p : (vec bool k) * bool) => g i [=] affine k (fst p) (snd p))).
  intro i.
  apply (counting_are_affine (H0 i)).
  pose (w := fun i => fst (projT1 (H1 i))).
  pose (c := fun i => snd (projT1 (H1 i))).
  pose (W := to_vec n w).
  pose (cbar := to_vec n c).
  exists (appl k n (transpose n k W) v).
  exists (xorb (dotprod n v cbar) b).
  intro x.
  unfold affine.
  rewrite <- xorb_assoc.
  rewrite <- assoc_lemma.
  rewrite <- dotprod_l_dist.
  unfold comp.
  rewrite Hf.
  simpl.
  unfold affine.
  f_equal.
  f_equal.
  apply vec_ext.
  intro i.
  rewrite vec_ap_lemma.
  transitivity (g i x).
  auto.
  rewrite vec_add_correct.
  f_equal.
  rewrite appl_correct.
  unfold W.
  rewrite (projT2 (H1 i)).
  unfold affine.
  unfold w, cbar.
  unfold c.
  simpl.
  rewrite to_vec_correct.
  rewrite to_vec_correct.
  reflexivity.
Qed.

(*only counting functions can be defined from a set of counting connectives*)
Lemma counting_upward_closed : upward_closed counting.
Proof.
  unfold upward_closed.
  intros.
  induction H.
  apply H.
  unfold counting.
  intro i.
  destruct i.
  intro j.
  destruct (index_dec n i j).
  right.
  rewrite H; apply eq_count.
  left.
  apply neq_dummy.
  exact H.
  apply counting_compose.
  exact IHDefinable.
  exact H1.
  intro i.
  destruct (IHDefinable i).
  left; intro v.
  rewrite <- H0.
  rewrite <- H0.
  apply H1.
  right; intro v.
  rewrite <- H0.
  rewrite <- H0.
  apply H1.
Qed.

Lemma not_fp_t : ~ f_preserving (fun x : vec bool 1 => true).
Proof.
  intro.
  absurd ((fun _ => true) [false] = false).
  discriminate.
  apply H.
Qed.

Lemma not_tp_f : ~ t_preserving (fun x : vec bool 1 => false).
Proof.
  intro.
  absurd ((fun _ => false) [true] = true).
  discriminate.
  apply H.
Qed.

Lemma not_mon_impl : ~ monotone IMPL.
Proof.
  intro.
  absurd (bool_le (IMPL [false , false]) (IMPL [true , false]) ).
  auto.
  apply H.
  simpl.
  auto.
Qed.

Lemma not_sd_and : ~ self_dual AND.
Proof.
  intro.
  absurd (AND [false , true] = negb (AND [true , false])).
  discriminate.
  apply H.
Qed.

Lemma not_counting_and : ~ counting AND.
Proof.
  intro.
  destruct (H (inl tt)).
  absurd (AND [false , true] = AND [true , true] ).
  discriminate.
  apply H0.
  absurd (AND [false , false] = negb (AND [true , false] )).
  discriminate.
  apply H0.
Qed.

Lemma closed_lemma(X Y: forall n:nat, conn n -> Prop) :
  FC X ->  upward_closed Y -> (forall (n : nat)(f : conn n), decidable0 (Y n f)) ->
  (exists (m : nat)(f : conn m), ~ Y m f) -> exists (n : nat)(g : conn n), X n g /\ ~ Y n g.
Proof.
  intros.
  destruct H2 as [n [g nYg]].
  pose (gdef := H n g).
  induction gdef.
  exists n,f.
  split.
  exact H2.
  exact nYg.
  apply IHgdef.
  intro.
  apply nYg.
  apply H0.
  apply null_def.
  apply atom_def.
  exact H2.
  elim nYg.
  apply H0.
  apply project.
  destruct (H1 n f).
  assert (decidable0 (exists i, ~ Y k (item_at (conn k) n i gs))).
  apply finExEM.
  intro i.
  apply dec_neg.
  intro h.
  apply H1.
  destruct H5.
  destruct H5 as [i Hi].
  apply (H3 i).
  exact Hi.
  elim nYg.
  apply H0.
  apply compose.
  apply atom_def.
  exact H4.
  intro i.
  apply atom_def.
  destruct (H1 k (item_at (conn k) n i gs)).
  exact H6.
  elim H5.
  exists i.
  exact H6.
  apply IHgdef.
  exact H4.
  apply IHgdef.
  intro.
  apply nYg.
  apply H0.
  assert (Definable Y f).
  apply atom_def.
  exact H3.
  apply (def_ext H4).
  exact H2.
Qed.

Theorem Post_FC_Part_Two(X : forall n:nat, conn n -> Prop) :
  FC X ->
  (non_fp X /\ non_tp X /\ non_mon X /\ non_sd X /\ non_counting X).
Proof.
  intro.
  split.
  apply (closed_lemma H).
  exact fp_upward_closed.
  apply fp_dec.
  exists 1,(fun x => true).
  apply not_fp_t.
  split.
  apply (closed_lemma H).
  exact tp_upward_closed.
  apply tp_dec.
  exists 2,(fun x => false).
  apply not_tp_f.
  split.
  apply (closed_lemma H).
  exact mon_upward_closed.
  apply mon_dec.
  exists 2,IMPL.
  apply not_mon_impl.
  split.
  apply (closed_lemma H).
  apply sd_upward_closed.
  apply sd_dec.
  exists 2,AND.
  apply not_sd_and.
  apply (closed_lemma H).
  apply counting_upward_closed.
  apply counting_dec.
  exists 2,AND.
  apply not_counting_and.
Qed.

Theorem Post_Functional_Completeness(X : forall n:nat, conn n -> Prop)  : FC X <->
  (non_fp X /\ non_tp X /\ non_mon X /\ non_sd X /\ non_counting X).
Proof.
  split.
  apply Post_FC_Part_Two.
  apply Post_FC_Part_One.
Qed.
